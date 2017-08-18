#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <system_error>
#include <algorithm>

#include <limits.h>
#include <sys/stat.h>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/TargetOptions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Parse/ParseAST.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/Core/Replacement.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Twine.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"

#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"

#include "llvm/Support/FileSystem.h"


typedef int* intptr;

enum locality {UNDEF, GLOBAL, CRITLOCAL, FUNLOCAL, ELSELOCAL}; // GLOBAL = global, CRITLOCAL = declared inside its critical section, FUNLOCAL = declared inside the function which contains its critical section, ELSELOCAL = declared non-globally but outside its critical section.

struct variable {
    std::string namestr;
    std::string typestr;
    bool array;
    enum locality locality;
    bool threadLocal;
    bool pointer;
    bool needsReturn;
};

struct criticalSection {
    //bool needsRefactoring;
    bool needsWait;
    bool noMsgStruct;
    std::string lockname;
    std::vector<struct variable*>* accessedvars;
    signed lockdepth;
    signed depth;
    clang::Stmt* lockstmt;
    clang::Stmt* unlockstmt;
    clang::Stmt* stmtabovelock;
    bool typeA;
    clang::FunctionDecl* funcwlock;
    clang::FunctionDecl* funcwunlock;
    bool transformed;
    std::vector<clang::Stmt*>* unlockstmts;
    std::vector<clang::Stmt*>* returnstmts;
    bool simplereturns;
    char type; // Can be 'U' = undefined, 'A' = type A, 'B' = type B, 'C' = type C.
    unsigned start; // Only for debugging purposes
    unsigned end;   // Only for debugging purposes
};

struct recursionStackEntry {
    clang::Stmt* stmt;
    unsigned iternum;
};

using namespace clang;
using namespace clang::tooling;

std::map<std::string, std::vector<Replacement>>* RepMap;
std::vector<struct criticalSection*> crits;

Stmt* thestmt;

/*unsigned critcount = 0;
unsigned transformed = 0;
unsigned acrits = 0;
unsigned bcrits = 0;
unsigned ccrits = 0;*/

Replacement createAdjustedReplacementForSR(SourceRange sr, ASTContext* TheContext, std::vector<Replacement>& repv, std::string text, bool injection, int newlength);

Replacement createInjectedReplacementForSR(SourceRange sr, ASTContext* TheContext, std::vector<Replacement>& repv, std::string text);

//Replacement createEndReplacement(ASTContext* TheContext, std::vector<Replacement>& repv, std::string text);

/* Returns true if sr1 < sr2, false otherwise */
bool isSRLessThan(SourceRange sr1, SourceRange sr2, ASTContext* TheContext);

/* Returns true if sr1 is contained completely inside sr2, false otherwise */
bool isSRInside(SourceRange sr1, SourceRange sr2, ASTContext* TheContext);

void printCrits(ASTContext* TheContext);

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class FindingASTVisitor : public RecursiveASTVisitor<FindingASTVisitor> {
private:
    ASTContext *TheContext;
public:
    FindingASTVisitor(ASTContext *C) : TheContext(C) {
        //LastContext = TheContext;
        std::vector<Replacement> vec;
        SourceManager& sm = TheContext->getSourceManager();
        StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
        char* fullpath = realpath(filename.str().c_str(), NULL);
        std::string filenamestr = std::string(fullpath);
        (*RepMap)[filenamestr] = vec; //Initializing the Replacement vector
        std::vector<Replacement> maprepv = (*RepMap)[filenamestr];
        Replacement newReplacement = Replacement(StringRef(filenamestr), 0, 0, "");
        //std::cout << "Upper filename: " << filenamestr << std::endl;
        maprepv.push_back(newReplacement); //Adding dummy replacement to prent crash when attempting o get unmodified buffer.
        (*RepMap)[filenamestr] = maprepv;
        free(fullpath);
    }

    void checkStatement(Stmt* stmt, struct criticalSection** newcrit, bool* inCrit, bool* needspush, bool* skip, unsigned depth, llvm::raw_string_ostream& os, std::string& nodestring, std::stringstream& nodetext, FunctionDecl* fdecl, unsigned fdepth, Stmt* stmt2) {
        if(*inCrit == false) {
            if(isa<CallExpr>(stmt)) {
                CallExpr* MyCallExpr = cast<CallExpr>(stmt);
                FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                if(MyFunDecl != 0) {
                    std::string name = MyFunDecl->getNameInfo().getName().getAsString();
                    if(name == "pthread_mutex_lock") {
                        //critcount++;
                        //std::cout << "Found!" << std::endl;
                        *inCrit = true;
                        *needspush = true;
                        //std::cout << "Setting needspush (is " << *needspush << ", could be " << needspush << ")..." << std::endl;
                        nodetext.str("");
                        nodestring = "";
                        (*newcrit) = new criticalSection;
                        (*newcrit)->accessedvars = (new std::vector<struct variable*>);
                        (*newcrit)->unlockstmts = (new std::vector<Stmt*>);
                        (*newcrit)->returnstmts = (new std::vector<Stmt*>);
                        (*newcrit)->lockstmt = stmt;
                        (*newcrit)->unlockstmt = NULL;
                        (*newcrit)->funcwlock = fdecl;
                        (*newcrit)->lockdepth = depth;
                        (*newcrit)->needsWait = false;
                        (*newcrit)->stmtabovelock = stmt2;
                        (*newcrit)->typeA = true;
                        (*newcrit)->type = 'U';
                        (*newcrit)->start = std::get<1>(FullSourceLoc(stmt->getLocStart(), TheContext->getSourceManager()).getDecomposedLoc());
                        (*newcrit)->transformed = false;
                        PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                        PrintingPolicy& ppr = pp;
                        MyCallExpr->getArg(0)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                        (*newcrit)->lockname = os.str();
                        //std::cout << "New lock has lockname \"" << (*newcrit)->lockname << "\"." << std::endl;
                        //std::cout << "Lockname: " << newcrit->lockname << std::endl;
                    }
                }
            } 
        } else {
            if(isa<CallExpr>(stmt)) {
                CallExpr* MyCallExpr = cast<CallExpr>(stmt);
                FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                if(MyFunDecl != 0) {
                    std::string name = MyFunDecl->getNameInfo().getName().getAsString();
                    if(name == "pthread_mutex_unlock") {
                        (*newcrit)->unlockstmts->push_back(stmt);
                        PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                        PrintingPolicy& ppr = pp;
                        nodestring = "";
                        MyCallExpr->getArg(0)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                        std::string lname = os.str();
                        //std::cout << "Comparing \"" << lname << "\" and \"" << (*newcrit)->lockname << "\"." << std::endl;
                        if(lname.compare((*newcrit)->lockname) == 0) {
                            (*newcrit)->unlockstmt = stmt;
                            (*newcrit)->funcwunlock = fdecl;
                            //(*newcrit)->depth = depth-(*newcrit)->depth;
                            (*newcrit)->depth = 0-((*newcrit)->lockdepth-depth);
                            if((*newcrit)->stmtabovelock != stmt2) {
                                (*newcrit)->typeA = false;
                            } else {
                                (*newcrit)->typeA = true;
                            }
                            (*newcrit)->end = std::get<1>(FullSourceLoc(stmt->getLocEnd(), TheContext->getSourceManager()).getDecomposedLoc());
                        }
                    } else if(name == "pthread_mutex_lock") {
                        if((*newcrit)->unlockstmt != NULL) {
                            crits.push_back((*newcrit));
                            //std::cout << "169 pushed " << (*newcrit) << "." << std::endl;
                            //critcount++;
                        } else {
                            delete (*newcrit);
                        }
                        //std::cout << "Pushed!" << std::endl;
                        *inCrit = false;
                        *needspush = false;
                        //std::cout << "Setting needspush (is " << *needspush << ", could be " << needspush << ")..." << std::endl;
                        *skip = true;
                    }
                } 
            } else if(isa<ReturnStmt>(stmt)) {
                (*newcrit)->returnstmts->push_back(stmt);
            } else if(isa<BreakStmt>(stmt)) {
                delete (*newcrit);
                *inCrit = false;
                *needspush = false;
                *skip = true;
            }
        }
    }
    
    void checkStatements(Stmt* stmt, struct criticalSection** newcrit, bool* inCrit, bool* needspush, bool* skip, unsigned depth, llvm::raw_string_ostream& os, std::string& nodestring, std::stringstream& nodetext, std::vector<FunctionDecl*>* fstack, std::vector<unsigned>* dstack) {
        //std::cout << "Depth: " << depth << ", type: " << stmt->getStmtClassName() << ", inCrit: " << *inCrit << " inside function '" << (*fstack)[fstack->size()-1]->getNameInfo().getAsString() << "'." << std::endl;
        if(isa<CallExpr>(stmt)) {
            CallExpr* cx = cast<CallExpr>(stmt);
            FunctionDecl* fdecl = cx->getDirectCallee();
            if(fdecl != 0) {
                fdecl = fdecl->getCanonicalDecl();
            }
            //std::cout << "About to enter function " << fdecl << " with body top stmt " << fdecl->getBody() << ", isDefined() = " << fdecl->isDefined() << " and willHaveBody() = " << fdecl->willHaveBody() << "." << std::endl;
            if(fdecl != NULL && fdecl->hasBody() == true) {
                std::string fname = fdecl->getNameInfo().getAsString();
                //std::cout << "Entering '" << fname << "'..." << std::endl;
                bool match = false;
                for(unsigned i = 0; i < fstack->size(); i++) {
                    if(fname.compare((*fstack)[i]->getNameInfo().getAsString()) == 0) {
                        match = true;
                        std::cout << "Aborting recursion to avoid infinite loop." << std::endl;
                    }
                }
                if(match == false) {
                    dstack->push_back(depth);
                    fstack->push_back(fdecl);
                    checkStatements(fdecl->getBody(), newcrit, inCrit, needspush, skip, 0, os, nodestring, nodetext, fstack, dstack);
                    fstack->pop_back();
                    depth = dstack->back();
                    dstack->pop_back();
                }
            }
        }
        Stmt::child_iterator ChildIterator = stmt->child_begin();
        while(ChildIterator != stmt->child_end()) {
            if(*ChildIterator != NULL) {
                checkStatement(*ChildIterator, newcrit, inCrit, needspush, skip, depth, os, nodestring, nodetext, (*fstack)[fstack->size()-1], fstack->size()-1, stmt);
            }
            if(*skip == false) {
                if(*ChildIterator != NULL) {
                    checkStatements(*ChildIterator, newcrit, inCrit, needspush, skip, depth+1, os, nodestring, nodetext, fstack, dstack);
                }
                ChildIterator++;
            } else {
                *skip = false;
            }
        }
    }

    bool VisitDecl(Decl *d) {
        if(isa<TranslationUnitDecl>(d)) {
            //d->dumpColor();
            TranslationUnitDecl* tud = cast<TranslationUnitDecl>(d);
            DeclContext::decl_iterator DeclIterator = tud->decls_begin();
            int i = 0;
            bool inCrit = false;
            bool skip = false;
            std::stringstream nodetext;
            std::string nodestring;
            llvm::raw_string_ostream os(nodestring);
            struct criticalSection* newcrit = NULL;
            bool needspush = false;
            std::vector<FunctionDecl*> fstack;
            std::vector<unsigned> dstack;
            while(DeclIterator != tud->decls_end()) {
                if(isa<FunctionDecl>(*DeclIterator)) {
                    //std::cout << "Func: " << i << std::endl;
                    //(*DeclIterator)->dumpColor();
                    FunctionDecl* funcdecl = cast<FunctionDecl>(*DeclIterator);
                    Stmt* funcbody = funcdecl->getBody();
                    if(funcbody != NULL) {
                        std::string fname = funcdecl->getNameInfo().getAsString();
                        fstack.push_back(funcdecl);
                        checkStatements(funcbody, &newcrit, &inCrit, &needspush, &skip, 0, os, nodestring, nodetext, &fstack, &dstack);
                        //std::cout << "Checking needspush (is " << needspush << ")..." << std::endl;
                        if(needspush == true) {
                            crits.push_back(newcrit);
                            //std::cout << "255 Pushed " << newcrit << "." << std::endl;
                            //critcount++;
                            needspush = false;
                            inCrit = false;
                        }
                        fstack.pop_back();
                    }
                    i++;
                }
                DeclIterator++;
            }
        }
        return true;
    }

    void fixCrits(ASTContext* TheContext) { // Crude fix for crits sometimes having invalid (NULL) unlock statements because pushing to repvec is flaky. Also removes duplicate crits. Also removes return statements which are actually outside the critical section but were detected as inside due to quirky crit detection.
        std::vector<struct criticalSection*>::iterator criterator = crits.begin();
        unsigned num = 0;
        bool erased = false;
        std::cout << "crits.size() == " << crits.size() << "." << std::endl;
        std::cout << "Crits go from " << *crits.begin() << " to " << *crits.end() << "." << std::endl;
        while(criterator != crits.end()) {
            std::cout << *criterator << " with lockstmt " << (*criterator)->lockstmt << std::endl;
            for(unsigned i = 0; i < crits.size(); i++) {
                if(num != i && *criterator == crits[i]) {
                    crits.erase(criterator);
                    criterator = crits.begin();
                    num = 0;
                    std::cout << "crits.size() == " << crits.size() << "." << std::endl;
                }
            }
            if(erased == false) {
                criterator++;
            } else {
                erased = false;
            }
            num++;
        }
        criterator = crits.begin();
        num = 0;
        erased = false;
        std::cout << "Crits go from " << *crits.begin() << " to " << *crits.end() << "." << std::endl;
        while(criterator != crits.end()) {
            std::cout << *criterator << " with lockstmt " << (*criterator)->lockstmt << std::endl;
            if((*criterator)->unlockstmt == NULL) {
                delete (*criterator)->unlockstmts;
                delete (*criterator)->returnstmts;
                delete *criterator;
                crits.erase(criterator);
                criterator = crits.begin();
                num = 0;
                std::cout << "crits.size() == " << crits.size() << "." << std::endl;
            } else {
                for(unsigned i = 0; i < crits.size(); i++) {
                    /*if(num != i) {
                        std::cout << (*criterator)->lockstmt << " == " << crits[i]->lockstmt << std::endl;
                        }*/
                    if(num != i && (*criterator)->lockstmt == crits[i]->lockstmt) {
                        std::cout << "Deleting " << *criterator << " with lockstmt " << (*criterator)->lockstmt << std::endl;
                        //delete *criterator;
                        crits.erase(criterator);
                        criterator = crits.begin();
                        num = 0;
                        std::cout << "crits.size() == " << crits.size() << "." << std::endl;
                    } 
                }
            }
            if(erased == false) {
                criterator++;
            } else {
                erased = false;
            }
            num++;
        }
        erased = false;
        for(unsigned i = 0; i < crits.size(); i++) {
            if(crits[i]->returnstmts->empty() == false) {
                std::vector<clang::Stmt*>::iterator riterator = crits[i]->returnstmts->begin();
                SourceRange lockrange = crits[i]->lockstmt->getSourceRange();
                SourceRange unlockrange = crits[i]->unlockstmt->getSourceRange();
                while(riterator != crits[i]->returnstmts->end()) {
                    //printf("End: %lX\n", crits[i]->returnstmts->end());
                    if((*riterator) != NULL) {
                        //printf("%lX\n", (*riterator));
                        SourceRange returnrange = (*riterator)->getSourceRange();
                        if(isSRLessThan(unlockrange, returnrange, TheContext) == true || isSRLessThan(returnrange, lockrange, TheContext) == true) {
                            crits[i]->returnstmts->erase(riterator);
                            erased = true;
                        }
                    }
                    if(erased == false) {
                        riterator++;
                    } else {
                        erased = false;
                    }
                }
            }
        }
    }
};

class ScanningASTVisitor : public RecursiveASTVisitor<ScanningASTVisitor> {
private:
    ASTContext *TheContext;
    TranslationUnitDecl* TheTUD;
public:
    ScanningASTVisitor(ASTContext *C) : TheContext(C) {}

    bool VisitStmt(Stmt *s) {
        if(isa<DeclRefExpr>(s) || isa<DeclStmt>(s)) {
            bool dre;
            bool dodo = true;
            SourceLocation sloc;
            bool array;
            std::string name;
            std::string tstr;
            std::string ctstr;
            clang::DeclStmt::decl_iterator DeclIterator;
            Decl* d;
            if(isa<DeclRefExpr>(s) == true && isa<EnumConstantDecl>(cast<DeclRefExpr>(s)->getDecl()) == false) {
                dre = true;
                Expr* e = cast<Expr>(s);
                DeclarationNameInfo declname = ((DeclRefExpr*)(e))->getNameInfo();
                name = declname.getName().getAsString();
                tstr = ((DeclRefExpr*)(e))->getDecl()->getType().getAsString();
                array = isa<ArrayType>(((DeclRefExpr*)(e))->getDecl()->getType().getDesugaredType((*TheContext)).getTypePtr());
                if(array == true) {
                    tstr = cast<ArrayType>(((DeclRefExpr*)(e))->getDecl()->getType().getDesugaredType((*TheContext)).getTypePtr())->getElementType().getAsString();
                }
                sloc = e->getExprLoc();
                d = ((DeclRefExpr*)(e))->getDecl();
            } else {
                dre = false;
                DeclIterator = ((DeclStmt*)(s))->decl_begin();
            }
            SourceManager& sm = TheContext->getSourceManager();
            //e->dump();
            //std::cout << std::get<1>(FullSourceLoc(e->getExprLoc(), sm).getDecomposedLoc()) << std::endl;
            //std::cout << sm.getPresumedLoc(sm.getSpellingLoc(e->getExprLoc())).getFilename() << " == " << sm.getFileEntryForID(sm.getMainFileID())->getName().str() << std::endl;
            //unsigned i = 0;
            if(s != NULL) {
                do {
                    if(dre == true) {
                        dodo = false;
                    } else {
                        if(DeclIterator != ((DeclStmt*)(s))->decl_end()) {
                            d = *DeclIterator;
                            if(isa<VarDecl>(d) == true && isa<EnumConstantDecl>(d) == false) {
                                name = cast<VarDecl>(d)->getNameAsString();
                                tstr = cast<VarDecl>(d)->getType().getAsString();
                                array = isa<ArrayType>(cast<VarDecl>(d)->getType().getDesugaredType((*TheContext)).getTypePtr());
                                if(array == true) {
                                    tstr = cast<ArrayType>(cast<VarDecl>(d)->getType().getDesugaredType((*TheContext)).getTypePtr())->getElementType().getAsString();
                                }
                                sloc = d->getLocation();
                            } else {
                                name = "";
                                tstr = "invalidinvalidinvalid++%&/"; // Most definitely not a valid type.
                            }
                            DeclIterator++;
                        } else {
                            dodo = false;
                        }
                    }
                    /*s->dump();
                    std::cout << std::get<1>(FullSourceLoc(sloc, sm).getDecomposedLoc()) << std::endl;
                    std::cout << sm.getPresumedLoc(sm.getSpellingLoc(sloc), false).getFilename() << " == " << sm.getFileEntryForID(sm.getMainFileID())->getName().str() << std::endl;*/
                    for(auto c : crits) {
                        /*std::string lfname = c->funcwlock->getNameInfo().getAsString();
                          std::string ulfname = c->funcwunlock->getNameInfo().getAsString();
                          std::cout << "Critical section " << i << " belonging to lock '" << c->lockname << "' detected, with length " << c->end-c->start << ", depth " << c->depth << ", lockdepth " << c->lockdepth << ", lockstatement '" << c->lockstmt << "' at position " << c->start << ", residing in function '" << lfname << "', and unlock statement '" << c->unlockstmt << "' at position " << c->end << ", residing in function '" << ulfname << "'." << std::endl;
                          i++;*/
                        if((sm.getPresumedLoc(sm.getSpellingLoc(sloc), false).isValid() == true) && (sm.getPresumedLoc(sm.getSpellingLoc(sloc), false).getFilename() == sm.getFileEntryForID(sm.getMainFileID())->getName()) && (FullSourceLoc(sloc, sm).isBeforeInTranslationUnitThan(c->unlockstmt->getLocStart()) == true && FullSourceLoc(c->lockstmt->getLocStart(), sm).isBeforeInTranslationUnitThan(sloc)) == true) {
                            //if(isa<FunctionDecl>(e->)
                            bool dup = false;
                            for(auto v : *(c->accessedvars)) {
                                if(v->namestr.compare(name) == 0) {
                                    dup = true;
                                }
                            }
                            const char* tstring = tstr.c_str();
                            if((dup == false) && (dre == false || isa<FunctionDecl>(d) == false)) {
                                struct variable* newvar = new struct variable;
                                //std::cout << "    Allocating variable at " << newvar << "..." << std::endl;
                                newvar->namestr = name;
                                //std::cout << "Name: " << name << std::endl;
                                newvar->typestr = tstr;
                                newvar->array = array;
                                //newvar->typestr = declname.getNamedTypeInfo()->getType().getAsString();
                                //std::cout << "Type: " << newvar->typestr << std::endl;
                                if(strstr(tstring, "*") != NULL) {
                                    newvar->pointer = true;
                                } else {
                                    newvar->pointer = false;
                                }
                                if(newvar->array) {
                                    newvar->typestr = newvar->typestr + " * ";
                                }
                                SourceRange declsr = d->getSourceRange();
                                newvar->threadLocal = false;
                                if((isSRLessThan(c->lockstmt->getSourceRange(), declsr, TheContext) == true) && (isSRLessThan(declsr, c->unlockstmt->getSourceRange(), TheContext) == true)) {
                                    newvar->locality = CRITLOCAL;
                                    newvar->needsReturn = false;
                                } else {
                                    if(TheTUD->containsDecl(d) == true) {
                                        newvar->locality = GLOBAL;
                                        newvar->threadLocal = ((strstr(tstring, "_Thread_local") != NULL) || (strstr(tstring, "thread_local")) != NULL || (strstr(tstring, "__thread") != NULL) || (strstr(tstring, "__declspec(thread)") != NULL));
                                        newvar->needsReturn = newvar->threadLocal;
                                    } else {
                                        if(isSRInside(declsr, c->funcwunlock->getBody()->getSourceRange(), TheContext) == true) {
                                            newvar->locality = FUNLOCAL;
                                            newvar->needsReturn = false;
                                        } else {
                                            newvar->locality = ELSELOCAL;
                                            if(newvar->pointer == true) {
                                                newvar->needsReturn = true;
                                            } else {
                                                newvar->needsReturn = false;
                                            }
                                        }
                                    }
                                }
                                if(newvar->locality == CRITLOCAL || newvar->locality == FUNLOCAL || newvar->locality == ELSELOCAL) {
                                    if(c->lockdepth == 0 && c->typeA == true) {
                                        Stmt::child_iterator ChildIterator = c->funcwunlock->getBody()->child_begin();
                                        /*std::cout << "c->unlockstmt = ";
                                        c->funcwunlock->getBody()->dumpPretty(*TheContext);
                                        std::cout << std::endl;
                                        bool ended = false;*/
                                        while(*ChildIterator != c->unlockstmt) {
                                            /*if(*ChildIterator != NULL && ended == false) {
                                                (*ChildIterator)->dumpPretty(*TheContext);
                                                std::cout << *ChildIterator << " == " << c->unlockstmt << std::endl;
                                            }
                                            if(ChildIterator == c->funcwunlock->getBody()->child_end()) {
                                                ended = true;
                                                }*/
                                            ChildIterator++;
                                        }
                                        while(ChildIterator != c->funcwunlock->getBody()->child_end()) {
                                            if(checkDeclRefsRecursive(*ChildIterator, tstr, name) == true) {
                                                newvar->needsReturn = true;
                                                break;
                                            }
                                            ChildIterator++;
                                        }
                                    } else {
                                        newvar->needsReturn = true; //STUB; unimplemented!
                                    }
                                }
                                if(newvar->needsReturn == true) {
                                    c->needsWait = true;
                                }
                                c->accessedvars->push_back(newvar);
                            }
                        }
                    } 
                } while(dodo == true); 
            }
        }
        return true;
    }

    bool checkDeclRefsRecursive(Stmt* s, std::string tstr, std::string name) {
        if(isa<DeclRefExpr>(s)) {
            DeclarationNameInfo declname2 = ((DeclRefExpr*)(s))->getNameInfo();
            std::string name2 = declname2.getName().getAsString();
            std::string tstr2 = ((DeclRefExpr*)(s))->getDecl()->getType().getAsString();
            //std::cout << tstr2 << " == " << tstr << " && " << name2 << " == " << name << std::endl;
            if(tstr2 == tstr && name2 == name) {
                return true;
            }
        } 
        if(s->child_begin() != s->child_end()) {
            Stmt::child_iterator ChildIterator = s->child_begin();
            while(ChildIterator != s->child_end()) {
                if(*ChildIterator != NULL && checkDeclRefsRecursive(*ChildIterator, tstr, name) == true) {
                    return true;
                }
                ChildIterator++;
            }
        }
        return false;
    }

    bool VisitDecl(Decl *d) {
        if(isa<TranslationUnitDecl>(d)) {
            TheTUD = cast<TranslationUnitDecl>(d);
        }
        return true;
    }
};

class ModifyingASTVisitor : public RecursiveASTVisitor<ModifyingASTVisitor> {
private:
    ASTContext *TheContext;
    SourceRange SRToAddProtosTo;
    bool SRset = false;
public:
    ModifyingASTVisitor(ASTContext *C) : TheContext(C) {}

    bool VisitDecl(Decl *d) {
        SourceManager& sm = TheContext->getSourceManager();
        if(isa<FunctionDecl>(d)) {
            if(((SRset == false) || (isSRLessThan(d->getSourceRange(), SRToAddProtosTo, TheContext) == true)) && sm.getPresumedLoc(sm.getSpellingLoc(d->getLocation()), false).getFilename() == sm.getFileEntryForID(sm.getMainFileID())->getName()) {
                SRToAddProtosTo = d->getSourceRange();
                SRset = true;
            }
        }
        return true;
    }

    /*void AddTypedefsAndGlobals() {
        for(unsigned i = 0; i < crits.size(); i++) {
            for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                std::stringstream nodetext;
                bool push = false;
                if(crits[i]->accessedvars->at(v)->cantypestr != crits[i]->accessedvars->at(v)->typestr) {
                    nodetext << "typedef " << crits[i]->accessedvars->at(v)->cantypestr << " " << crits[i]->accessedvars->at(v)->typestr << ";\n\n";
                    push = true;
                }
                if(crits[i]->accessedvars->at(v)->locality == GLOBAL) {
                    nodetext << crits[i]->accessedvars->at(v)->typestr << " " << crits[i]->accessedvars->at(v)->namestr << ";\n\n";
                    push = true;
                }
                if(push == true) {
                    SourceManager& sm = TheContext->getSourceManager();
                    StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                    std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                    Replacement rep = createAdjustedReplacementForSR(SRToAddTo, TheContext, maprepv, nodetext.str(), true, 0);                maprepv.push_back(rep);
                    (*RepMap)[filename.str()] = maprepv;
                }
            }
        }
    }*/

    void AddStructs(bool addEmptyStructs, bool addStructs) {
        std::cout << "Adding structs..." << std::endl;
        for(unsigned i = 0; i < crits.size(); i++) {
            std::stringstream nodetext;
            std::stringstream pnodetext;
            std::string lfname = crits[i]->funcwlock->getNameInfo().getAsString();
            pnodetext << "struct " << lfname << "_critSec" << i << "_msg;\n";
            if(i == 0) {
                pnodetext << "\n";
            }
            nodetext << "struct " << lfname << "_critSec" << i << "_msg {\n";
            unsigned varcount = 0;
            for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                if(((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL) || ((*(crits[i]->accessedvars))[v]->locality == FUNLOCAL) || (((*(crits[i]->accessedvars))[v]->locality == CRITLOCAL) && ((*(crits[i]->accessedvars))[v]->needsReturn == true))) {
                    if((*(crits[i]->accessedvars))[v]->needsReturn == true) {
                        nodetext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " * " << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    } else {
                        nodetext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " " << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    }
                    varcount++;
                }
            }
            if(crits[i]->returnstmts->empty() == false) {
                if(crits[i]->simplereturns == true) {
                    nodetext << "    " << crits[i]->funcwunlock->getReturnType().getLocalUnqualifiedType().getAsString() << " * __retval__;\n    int * __earlyReturn__;\n";
                } 
            }
            nodetext << "};\n\n";
            if(addStructs == true) {
                if(varcount > 0 || addEmptyStructs == true) {
                    crits[i]->noMsgStruct = false;
                    SourceManager& sm = TheContext->getSourceManager();
                    StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                    std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                    //std::cout << "Function " << crits[i]->funcwlock->getNameInfo().getAsString() << " goes from " << crits[i]->funcwlock->getSourceRange().getBegin().printToString(sm) << " to " << crits[i]->funcwlock->getSourceRange().getEnd().printToString(sm) << ".\n";
                    //SourceRange bodysr = crits[i]->funcwlock->getBody()->getSourceRange();
                    //SourceLocation addsl = sm.translateFileLineCol(sm.getFileEntryForID(sm.getMainFileID()), FullSourceLoc(bodysr.getBegin(), sm).getExpansionLineNumber()-1, 1);
                    SourceLocation addsl = crits[i]->funcwlock->getDefinition()->getSourceRange().getBegin();
                    Replacement rep = createAdjustedReplacementForSR(SourceRange(addsl, addsl), TheContext, maprepv, nodetext.str(), true, 0);
                    //createInjectedReplacementForSR(crits[i]->funcwlock->getSourceRange(), TheContext, maprepv, nodetext.str());
                    Replacement rep2 = createAdjustedReplacementForSR(SRToAddProtosTo, TheContext, maprepv, pnodetext.str(), true, 0);
                    if(crits[i]->returnstmts->empty() == true || crits[i]->simplereturns == true) {
                        maprepv.push_back(rep2);
                        maprepv.push_back(rep);
                    }
                    (*RepMap)[filename.str()] = maprepv;
                } else {
                    crits[i]->noMsgStruct = true;
                }
            } else {
                if(varcount > 0 || addEmptyStructs == true) {
                    //std::cout << "Critical section " << i << " has a message struct." << std::endl;
                    crits[i]->noMsgStruct = false;
                    //std::cout << "noMsgStruct: " << crits[i]->noMsgStruct << std::endl;
                } else {
                    //std::cout << "Critical section " << i << " has no message struct." << std::endl;
                    crits[i]->noMsgStruct = true;
                    //std::cout << "noMsgStruct: " << crits[i]->noMsgStruct << std::endl;
                }
            }
        }
    }

    void TransformFunctions() {
        std::cout << "Transforming functions..." << std::endl;
        std::string headerinclude = "#include \"locks/locks.h\"\n\n";
        SourceManager& sm = TheContext->getSourceManager();
        StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
        std::vector<Replacement> mrv = (*RepMap)[filename.str()];
        Replacement headerrep = Replacement(filename, 0, 0, StringRef(headerinclude));
        mrv.push_back(headerrep);
        (*RepMap)[filename.str()] = mrv;
        for(unsigned i = 0; i < crits.size(); i++) {
            std::stringstream nodetext;
            std::stringstream functext;
            std::stringstream functext2;
            Replacement deleterep;
            Replacement firstrep;
            std::string structname;
            std::string lfname = crits[i]->funcwlock->getNameInfo().getAsString();
            if(crits[i]->returnstmts->empty() == false) {
                crits[i]->needsWait = true;
                crits[i]->simplereturns = true;
                for(unsigned j = 0; j < crits[i]->returnstmts->size(); j++) {
                    if(cast<ReturnStmt>(crits[i]->returnstmts->at(j))->getRetValue() != NULL) {
                        //std::cout << cast<ReturnStmt>(crits[i]->returnstmts->at(j))->getRetValue()->getType().getLocalUnqualifiedType().getAsString() << " == " << crits[i]->funcwunlock->getReturnType().getLocalUnqualifiedType().getAsString() << std::endl;
                        if(cast<ReturnStmt>(crits[i]->returnstmts->at(j))->getRetValue()->getType().getLocalUnqualifiedType() == crits[i]->funcwunlock->getReturnType().getLocalUnqualifiedType()) {
                                
                        } else {
                            crits[i]->simplereturns = false;
                        }
                    }
                }
                /*std::cout << "simplereturns: ";
                if(crits[i]->simplereturns == true) {
                    std::cout << "true" << std::endl;
                } else {
                    std::cout << "false" << std::endl;
                }*/
            }
            if(crits[i]->noMsgStruct == false) {
                std::stringstream sns;
                sns << lfname << "_cs" << i << "msg";
                structname = sns.str();
                nodetext << "struct " << lfname << "_critSec" << i << "_msg " << structname << ";\n";
                for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                    if((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL || (*(crits[i]->accessedvars))[v]->locality == FUNLOCAL) {
                        if((*(crits[i]->accessedvars))[v]->needsReturn == true && (*(crits[i]->accessedvars))[v]->array == false) {
                            nodetext << "    " << structname << "." << (*(crits[i]->accessedvars))[v]->namestr << " = &" << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                        } else {
                            nodetext << "    " << structname << "." << (*(crits[i]->accessedvars))[v]->namestr << " = " << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                        }
                    } else if((*(crits[i]->accessedvars))[v]->locality == CRITLOCAL && (*(crits[i]->accessedvars))[v]->needsReturn == true) {
                        nodetext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " " << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                        nodetext << "    " << structname << "." << (*(crits[i]->accessedvars))[v]->namestr << " = &" << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    } 
                }
            }
            functext2 << "void " << lfname << "_critSec" << i << "(unsigned int sz, void* msgP);\n";
            if(i == 0) {
                functext2 << "\n";
            }
            functext << "void " << lfname << "_critSec" << i << "(unsigned int sz, void* msgP) {\n";
            if(crits[i]->noMsgStruct == false) {
                functext << "    struct " << lfname << "_critSec" << i << "_msg* " << lfname << "_cs" << i << "msg = (struct " << lfname << "_critSec" << i << "_msg*)msgP;\n";
                for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                    if((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL || (*(crits[i]->accessedvars))[v]->locality == FUNLOCAL) {
                        if((*(crits[i]->accessedvars))[v]->needsReturn == true) {
                            if((*(crits[i]->accessedvars))[v]->array == false) {
                                functext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " " << (*(crits[i]->accessedvars))[v]->namestr << " = *(" << structname << "->" << (*(crits[i]->accessedvars))[v]->namestr << ");\n";
                            } else {
                                functext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " * " << (*(crits[i]->accessedvars))[v]->namestr << " = " << structname << "->" << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                            }
                        } else {
                            functext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " " << (*(crits[i]->accessedvars))[v]->namestr << " = " << structname << "->" << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                        }
                    } 
                }
                /*if(crits[i]->returnstmts->empty() == false) {
                    if(crits[i]->simplereturns == true) {
                        functext << "    " << lfname << "_cs" << i << "msg->__retval__ = NULL;\n    " << lfname << "_cs" << i << "msg->__earlyReturn__ = 0;\n";
                    }
                }*/
            }
            //unsigned currdepth;
            std::vector<struct recursionStackEntry> lstack;
            std::vector<struct recursionStackEntry> ulstack;
            struct recursionStackEntry rse;
            unsigned iternum = 0;
            rse.iternum = 0;
            Stmt* topBody = crits[i]->funcwlock->getBody();
            Stmt* currBody = topBody;
            Stmt* stmtafterlock;
            Stmt::child_iterator topIterator = topBody->child_begin();
            Stmt::child_iterator currIterator = topIterator;
            if(crits[i]->noMsgStruct == false) {
                nodetext << "    ";
            }
            if(crits[i]->returnstmts->empty() == false) {
                if(crits[i]->simplereturns == true) {
                    nodetext << "int __earlyReturn__ = 0;\n    " << crits[i]->funcwunlock->getReturnType().getLocalUnqualifiedType().getAsString() << " __retval__ = NULL;\n    " << lfname << "_cs" << i << "msg.__earlyReturn__ = &__earlyReturn__;\n    " << lfname << "_cs" << i << "msg.__retval__ = &__retval__;\n    ";
                }
            }
            if(crits[i]->needsWait == true) {
                nodetext << "LL_delegate_wait(";
            } else {
                //nodetext << "LL_delegate_wait(";
                nodetext << "LL_delegate(";
            }
            nodetext << crits[i]->lockname << ", " << lfname << "_critSec" << i;
            if(crits[i]->noMsgStruct == false) {
                nodetext << ", sizeof(" << structname << "), &" << structname << ");\n";
                /*for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                    if(((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL || (*(crits[i]->accessedvars))[v]->locality == FUNLOCAL) && (*(crits[i]->accessedvars))[v]->needsReturn == true) {
                        nodetext << "    " << (*(crits[i]->accessedvars))[v]->namestr << " = " << lfname << "_cs" << i << "msg." << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    } else if((*(crits[i]->accessedvars))[v]->locality == CRITLOCAL && (*(crits[i]->accessedvars))[v]->needsReturn == true) {
                        nodetext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " " << (*(crits[i]->accessedvars))[v]->namestr << " = " << lfname << "_cs" << i << "msg." << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    }
                }*/
                /*for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                    if((*(crits[i]->accessedvars))[v]->locality == CRITLOCAL && (*(crits[i]->accessedvars))[v]->needsReturn == true) {
                        nodetext << "    " << (*(crits[i]->accessedvars))[v]->namestr << " = *(" << lfname << "_cs" << i << "msg." << (*(crits[i]->accessedvars))[v]->namestr << ");\n";
                    }
                }*/
                if(crits[i]->returnstmts->empty() == false) {
                    if(crits[i]->simplereturns == true) {
                        nodetext << "    if(__earlyReturn__ != 0) {\n        return __retval__;\n    }\n\n";
                    } 
                }   
            } else {
                nodetext << ", 0, NULL);\n";
            }
            nodetext << "    ";
            bool first = true;
            //std::cout << "Checking..." << std::endl;
            //unsigned startoffset = 0;
            //unsigned headerlength = 0;
            //unsigned headerlength = functext.str().length();
            //std::cout << "headerlength: " << headerlength << std::endl;
            //std::cout << "functext.str(): \n" << functext.str() << std::endl;
            //std::cout << "headerlength: " << headerlength << std::endl;
            if(crits[i]->depth == 0 && crits[i]->typeA == true) {
                crits[i]->type = 'A';
                topBody = crits[i]->stmtabovelock;
                topIterator = topBody->child_begin();
                currBody = topBody;
                currIterator = topIterator;
                //std::cout << "Checked, case 1." << std::endl;
                //transformed++;
                //acrits++;
                unsigned bodystartpos;
                unsigned bodyendpos;
                // Flat case
                while(*topIterator != crits[i]->lockstmt && topIterator != topBody->child_end()) {
                    topIterator++;
                    iternum++;
                }
                topIterator++;
                stmtafterlock = *topIterator;
                while(*topIterator != crits[i]->unlockstmt) {
                    /*if(startoffset == 0) {
                        startoffset = sm.getFileOffset(FullSourceLoc(sm.getFileLoc((*topIterator)->getSourceRange().getBegin()), sm));
                        std::cout << "startoffset: " << startoffset << std::endl;
                    }*/
                    //(*topIterator)->dump();
                    //bool isUnlock = false;
                    std::string nodestring;
                    PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                    PrintingPolicy& ppr = pp;
                    llvm::raw_string_ostream os(nodestring);
                    (*topIterator)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                    //if(isUnlock == false) {
                        functext << "    " << os.str() << ";\n";
                    //}
                    SourceRange locksr = crits[i]->lockstmt->getSourceRange();
                    std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                    if(first == false) {
                        /*Replacement rep = createAdjustedReplacementForSR(sr, TheContext, maprepv, "", false, nodestring.length()+2);
                          maprepv.push_back(rep);
                          FullSourceLoc fslend = FullSourceLoc((*topIterator)->getSourceRange().getEnd(), sm);
                          bodyendpos = std::get<1>(fslend.getDecomposedLoc());
                          std::cout << "bodyendpos: " << bodyendpos << std::endl;*/
                    } else {
                        nodestring = "";
                        crits[i]->lockstmt->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                        firstrep = createAdjustedReplacementForSR(locksr, TheContext, maprepv, nodetext.str(), false, os.str().length()+2);
                        /*FullSourceLoc fslstart = FullSourceLoc((*topIterator)->getSourceRange().getBegin(), sm);
                          bodystartpos = std::get<1>(fslstart.getDecomposedLoc());
                          maprepv.push_back(rep);*/
                        first = false;
                    }
                    (*RepMap)[filename.str()] = maprepv;
                    topIterator++;
                    iternum++;
                }
                if(topIterator == topBody->child_end()) {
                    //transformed--;
                    //critcount--;
                    //acrits--;
                } else {
                    if(crits[i]->noMsgStruct == false) {
                        for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                            if(((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL || (*(crits[i]->accessedvars))[v]->locality == FUNLOCAL || (*(crits[i]->accessedvars))[v]->locality == CRITLOCAL) && (*(crits[i]->accessedvars))[v]->needsReturn == true && (*(crits[i]->accessedvars))[v]->array == false) {
                                functext << "    *(" << structname << "->" << (*(crits[i]->accessedvars))[v]->namestr << ") = " << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                            }
                        }
                    }
                    SourceManager& sm = TheContext->getSourceManager();
                    FullSourceLoc fslstart = FullSourceLoc(stmtafterlock->getLocStart(), sm);
                    FullSourceLoc fslend = FullSourceLoc(crits[i]->unlockstmt->getLocEnd(), sm);
                    bodystartpos = std::get<1>(fslstart.getDecomposedLoc());
                    bodyendpos = std::get<1>(fslend.getDecomposedLoc());
                    StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                    deleterep = Replacement(filename, bodystartpos, bodyendpos-bodystartpos+2, StringRef(""));
                    std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                
                    functext << "}\n\n";
                    //Replacement funcrep = createEndReplacement(TheContext, maprepv, functext.str());
                    std::string funcrepstr = functext.str();
                    std::string::size_type offset = funcrepstr.find("pthread_mutex_", 0);
                    unsigned j = 0;
                    while(offset != std::string::npos && j < crits[i]->unlockstmts->size()) {           
                        std::cout << "offset: " << offset << std::endl;
                        std::cout << funcrepstr.substr(offset, strlen("pthread_mutex_")) << std::endl;
                        std::string nodestr2;
                        llvm::raw_string_ostream os2(nodestr2);
                        CallExpr* MyCallExpr = cast<CallExpr>(crits[i]->unlockstmts->at(j));
                        //FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                        PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                        PrintingPolicy& ppr = pp;
                        MyCallExpr->getArg(0)->printPretty(os2, (PrinterHelper*)NULL, ppr, (unsigned)4);
                        std::string lname = os2.str();
                        //std::cout << "Comparing \"" << lname << "\" and \"" << (*newcrit)->lockname << "\"." << std::endl;
                        if(lname.compare(crits[i]->lockname) == 0) {
                            funcrepstr.replace(offset, strlen("pthread_mutex_unlock(")+lname.length()+strlen(");\n"), "");
                        } else {
                            funcrepstr.replace(offset, strlen("pthread_mutex_"), "LL_");
                        }
                        j++;
                        offset = funcrepstr.find("pthread_mutex_", offset);
                    }
                    if(crits[i]->returnstmts->empty() == false) {
                        offset = funcrepstr.find("return ", 0);
                        //std::cout << "roffset1: " << offset;
                        j = 0;
                        while(offset != std::string::npos && j < crits[i]->returnstmts->size()) {
                            //std::cout << "roffset: " << offset;
                            long replength = 0;
                            if(cast<ReturnStmt>(crits[i]->returnstmts->at(j))->getRetValue() != NULL) {
                                if(cast<ReturnStmt>(crits[i]->returnstmts->at(j))->getRetValue()->getType().getLocalUnqualifiedType() == crits[i]->funcwunlock->getReturnType().getLocalUnqualifiedType()) {
                                    unsigned length = sm.getFileOffset(FullSourceLoc(sm.getFileLoc(crits[i]->returnstmts->at(j)->getSourceRange().getEnd()), sm))-sm.getFileOffset(FullSourceLoc(sm.getFileLoc(crits[i]->returnstmts->at(j)->getSourceRange().getBegin()), sm))+2;
                                    std::string nodestr2;
                                    llvm::raw_string_ostream os2(nodestr2);
                                    //FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                                    PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                                    PrintingPolicy& ppr = pp;
                                    cast<ReturnStmt>(crits[i]->returnstmts->at(j))->getRetValue()->printPretty(os2, (PrinterHelper*)NULL, ppr, (unsigned)4);
                                    std::stringstream reptext;
                                    reptext << "    *(" << structname << "->__retval__) = " << os2.str() << ";\n    *(" << structname << "->__earlyReturn__) = 1;\n    return;\n";
                                    funcrepstr.replace(offset, length, reptext.str());
                                    replength = reptext.str().length();
                                    //std::cout << "Postrep: " << funcrepstr.substr(offset+replength, funcrepstr.length()) << std::endl;
                                } else {
                                    std::cout << "Complicated return detected." << std::endl;
                                }
                            } else {
                                std::cout << "NULL return detected, i = " << i << ", j = " << j << "." << std::endl;
                            }
                            j++;
                            offset = funcrepstr.find("return ", offset+replength);
                        }
                    }
                    //SourceRange bodysr = crits[i]->funcwlock->getBody()->getSourceRange();
                    //SourceLocation addsl = sm.translateFileLineCol(sm.getFileEntryForID(sm.getMainFileID()), FullSourceLoc(bodysr.getBegin(), sm).getExpansionLineNumber()-1, 1);
                    SourceLocation addsl = crits[i]->funcwlock->getDefinition()->getSourceRange().getBegin();
                    Replacement funcrep = createAdjustedReplacementForSR(SourceRange(addsl, addsl), TheContext, maprepv, funcrepstr, true, 0);
                    Replacement funcrep2 = createAdjustedReplacementForSR(SRToAddProtosTo, TheContext, maprepv, functext2.str(), true, 0);
                    if(crits[i]->returnstmts->empty() == true || crits[i]->simplereturns == true) {
                        maprepv.push_back(funcrep);
                        maprepv.push_back(funcrep2);
                        maprepv.push_back(deleterep);
                        maprepv.push_back(firstrep);
                        crits[i]->transformed = true;
                        //std::cout << "Pushed to " << filename.str() << "." << std::endl;
                    }
                    (*RepMap)[filename.str()] = maprepv;
                }
            } else if(crits[i]->funcwlock == crits[i]->funcwunlock) { // For counting mechanism
                //bcrits++;
                crits[i]->type = 'B';
            } else if(crits[i]->funcwlock == crits[i]->funcwunlock && false == true) { // WIP code disabled.
                if(crits[i]->lockdepth < 0) {
                    while(lstack.empty() == false || topIterator != topBody->child_end()) {
                        if(currIterator == currBody->child_end()) {
                            if(*currIterator == crits[i]->lockstmt) {
                                break;
                            } else {
                                if((*(*currIterator)->child_begin()) != NULL) {
                                    rse.stmt = currBody;
                                    rse.iternum = iternum;
                                    lstack.push_back(rse);
                                    currBody = (*currIterator);
                                    iternum = 0;
                                    currIterator = currBody->child_begin();
                                } else {
                                    currIterator++;
                                    iternum++;
                                }
                            }
                        } else {
                            rse = lstack[lstack.size()-1];
                            lstack.pop_back();
                            currBody = rse.stmt;
                            iternum = rse.iternum;
                            currIterator = currBody->child_begin();
                            for(unsigned j = 0; j < iternum; j++) {
                                currIterator++;
                            }
                        }
                    }
                }
                topBody = crits[i]->funcwunlock->getBody();
                currBody = topBody;
                topIterator = topBody->child_begin();
                currIterator = topIterator;
                while(ulstack.empty() == false || topIterator != topBody->child_end()) {
                    if(currIterator == currBody->child_end()) {
                        if(*currIterator == crits[i]->unlockstmt) {
                            break;
                        } else {
                            if((*(*currIterator)->child_begin()) != NULL) {
                                rse.stmt = currBody;
                                rse.iternum = iternum;
                                ulstack.push_back(rse);
                                currBody = (*currIterator);
                                iternum = 0;
                                currIterator = currBody->child_begin();
                            } else {
                                currIterator++;
                                iternum++;
                            }
                        }
                    } else {
                        rse = ulstack[ulstack.size()-1];
                        ulstack.pop_back();
                        currBody = rse.stmt;
                        iternum = rse.iternum;
                        currIterator = currBody->child_begin();
                        for(unsigned j = 0; j < iternum; j++) {
                            currIterator++;
                        }
                    }
                }
                if(crits[i]->lockdepth < 0) {
                    std::vector<Replacement> deleterepvec;
                    SourceRange startsr;
                    SourceRange endsr;
                    unsigned bodystartpos;
                    unsigned bodyendpos;
                    bool second = true;
                    Stmt* currTarget;
                    for(unsigned j = 0; j < ulstack.size(); j++) {
                        if(j != ulstack.size()-1) {
                            currTarget = ulstack[j].stmt;
                        } else {
                            currTarget = crits[i]->lockstmt;
                        }
                        while(*currIterator != currTarget) {
                            bool isUnlock = false;
                            if(isa<CallExpr>(*currIterator)) {
                                CallExpr* MyCallExpr = cast<CallExpr>(*currIterator);
                                std::string name = MyCallExpr->getDirectCallee()->getNameInfo().getName().getAsString();
                                if(name == "pthread_mutex_unlock") {
                                    PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                                    PrintingPolicy& ppr = pp;
                                    std::string nodestring;
                                    llvm::raw_string_ostream os(nodestring);
                                    MyCallExpr->getArg(0)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                                    std::string lname = os.str();
                                    if(lname.compare(crits[i]->lockname) == 0) {
                                        isUnlock = true;
                                    } else {
                                        for(unsigned j = 0; j < crits.size(); j++) {
                                            for(unsigned v = 0; v < crits[j]->accessedvars->size(); v++) {
                                                if((*(crits[j]->accessedvars))[v]->typestr.compare("pthread_mutex_t") == 0) {
                                                    if(lname.compare((*(crits[j]->accessedvars))[v]->namestr) == 0) {
                                                        isUnlock = true;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            std::string nodestring;
                            PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                            PrintingPolicy& ppr = pp;
                            llvm::raw_string_ostream os(nodestring);
                            (*currIterator)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                            if(isUnlock == false) {
                                functext << "    " << os.str() << ";\n";
                            }
                            SourceRange locksr = crits[i]->lockstmt->getSourceRange();
                            SourceManager& sm = TheContext->getSourceManager();
                            StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                            std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                            if(first == false) {
                                if(second == true) {
                                    startsr = (*currIterator)->getSourceRange();
                                    second = false;
                                }
                                endsr = (*currIterator)->getSourceRange();
                            } else {
                                nodestring = "";
                                crits[i]->lockstmt->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                                firstrep = createAdjustedReplacementForSR(locksr, TheContext, maprepv, nodetext.str(), false, os.str().length()+2);
                                /*FullSourceLoc fslstart = FullSourceLoc((*topIterator)->getSourceRange().getBegin(), sm);
                                  bodystartpos = std::get<1>(fslstart.getDecomposedLoc());
                                  maprepv.push_back(rep);*/
                                first = false;
                            }
                            currIterator++;
                        }
                        SourceManager& sm = TheContext->getSourceManager();
                        StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                        FullSourceLoc fslstart = FullSourceLoc(startsr.getBegin(), sm);
                        bodystartpos = std::get<1>(fslstart.getDecomposedLoc());
                        FullSourceLoc fslend = FullSourceLoc(endsr.getEnd(), sm);
                        bodyendpos = std::get<1>(fslend.getDecomposedLoc());
                        deleterep = Replacement(filename, bodystartpos, bodyendpos-bodystartpos+2, StringRef(""));
                        deleterepvec.push_back(deleterep);
                    }
                }
                // Same function case
            } else {
                crits[i]->type = 'C';
                //ccrits++;
                // Different function case
            }
            SourceManager& sm = TheContext->getSourceManager();
            StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
            std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
            //Replacement rep = createAdjustedReplacementForSR(SRToAddTo, TheContext, maprepv, functext.str(), true, 0);
            //maprepv.push_back(rep);
            (*RepMap)[filename.str()] = maprepv;
        }
    }
};

class FinalizingASTVisitor : public RecursiveASTVisitor<FinalizingASTVisitor> {
private:
    ASTContext *TheContext;
public:
    FinalizingASTVisitor(ASTContext *C) : TheContext(C) {}

    bool VisitExpr(Expr *e) {
        if(isa<CallExpr>(e)) {
            CallExpr* MyCallExpr = cast<CallExpr>(e);
            FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
            if(MyFunDecl != 0) {
                std::string name = MyFunDecl->getNameInfo().getName().getAsString();
                if(name == "pthread_mutex_init" || name == "pthread_mutex_destroy" || name == "pthread_mutex_lock" || name == "pthread_mutex_unlock") {
                    std::string nodestring;
                    llvm::raw_string_ostream os(nodestring);
                    PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                    PrintingPolicy& ppr = pp;
                    MyCallExpr->getArg(0)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                    std::string lname = os.str();
                    //bool isQD = false;
                    bool isTransformed = false;
                    for(unsigned c = 0; c < crits.size(); c++) {
                        /*if(lname.compare(crits[c]->lockname) == 0) {
                            isQD = true;
                        }*/
                        //printf("MyCallExpr: %lX, crits[%u]->lockstmt: %lX, crits[%u]->unlockstmt: %lX\n", MyCallExpr, c, crits[c]->lockstmt, c, crits[c]->unlockstmt);
                        if((MyCallExpr == crits[c]->lockstmt || MyCallExpr == crits[c]->unlockstmt) && crits[c]->transformed == true) {
                            isTransformed = true;
                        } else if(crits[c]->transformed == true) {
                            SourceManager& sm = TheContext->getSourceManager();
                            unsigned lockoffset = sm.getFileOffset(FullSourceLoc(sm.getFileLoc(crits[c]->lockstmt->getSourceRange().getBegin()), sm));
                            unsigned unlockoffset = sm.getFileOffset(FullSourceLoc(sm.getFileLoc(crits[c]->unlockstmt->getSourceRange().getBegin()), sm));
                            unsigned calloffset = sm.getFileOffset(FullSourceLoc(sm.getFileLoc(MyCallExpr->getSourceRange().getBegin()), sm));
                            printf("%u >= %u && %u <= %u\n", calloffset, lockoffset, calloffset, unlockoffset);
                            if(calloffset >= lockoffset && calloffset <= unlockoffset) { // NOTE: These conditions would be unsufficient to detect whether a call is located inside a transformed type C critical section or not, but this is okay for now since QDTrans doesn't currently transform any type C critical sections.
                                isTransformed = true;
                            }
                        }
                    }
                    bool push = false;
                    if(/*isQD == */true) {
                        std::stringstream newnode;
                        SourceManager& sm = TheContext->getSourceManager();
                        unsigned length = sm.getFileOffset(FullSourceLoc(e->getSourceRange().getEnd(), sm))-sm.getFileOffset(FullSourceLoc(e->getSourceRange().getBegin(), sm));
                        length += 3;
                        if(name == "pthread_mutex_init") {
                            newnode << "LL_initialize(" << lname << ");\n";
                            //length = 28+lname.length();
                            //length = 16+lname.length();
                            push = true;
                        } else if(name == "pthread_mutex_lock") {
                            newnode << "LL_lock(" << lname << ");\n";
                            //length = 0;
                            push = !isTransformed;
                        } else if(name == "pthread_mutex_unlock") {
                            newnode << "LL_unlock(" << lname << ");\n";
                            //length = 18+lname.length();
                            push = !isTransformed;
                        } else {
                            //newnode << "LL_destroy(" << lname << ");\n";
                            newnode << ""; // Fix for weird issue, shouldn't matter since LL_destroy doesn't actually do anything.
                            //length = 25+lname.length();
                            //length = 19+lname.length();
                            push = false;
                        }
                        //e->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                        if(push == true) {
                            StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                            std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                            Replacement rep = createAdjustedReplacementForSR(e->getSourceRange(), TheContext, maprepv, newnode.str(), true, length);
                            maprepv.push_back(rep);
                            (*RepMap)[filename.str()] = maprepv;
                        }
                    }
                }
            }
        }
        return true;
    }

    bool VisitDecl(Decl *d) {
        if(isa<VarDecl>(d) || isa<FieldDecl>(d)) {
            std::string typestr;
            if(isa<VarDecl>(d)) {
                VarDecl* vd = cast<VarDecl>(d);
                typestr = vd->getType().getAsString();
            } else {
                FieldDecl* fd = cast<FieldDecl>(d);
                typestr = fd->getType().getAsString();
            }
            if(typestr.compare("pthread_mutex_t") == 0) {
                bool isQD = false;
                NamedDecl* nd = cast<NamedDecl>(d);
                std::string declname = nd->getName().str();
                for(unsigned c = 0; c < crits.size(); c++) {
                    std::cout << "if(" << crits[c]->lockname << ".find(" << declname << ", 0)" << std::endl;
                    if(crits[c]->lockname.find(declname, 0) != std::string::npos && declname != "") {
                        isQD = true;
                        break;
                    }
                }
                if(isQD == true) {
                    SourceManager& sm = TheContext->getSourceManager();
                    SourceLocation dloc = d->getLocation();
                    if(sm.getPresumedLoc(sm.getSpellingLoc(dloc), false).getFilename() == sm.getFileEntryForID(sm.getMainFileID())->getName()) {
                        std::stringstream newnode;
                        newnode << "QDLock " << declname << ";\n";
                        StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                        std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                        Replacement rep = createAdjustedReplacementForSR(d->getSourceRange(), TheContext, maprepv, newnode.str(), true, declname.length()+18);
                        maprepv.push_back(rep);
                        (*RepMap)[filename.str()] = maprepv;
                    } else {
                        std::cout << "Lock " << declname << "'s declaration is inside file " << sm.getPresumedLoc(sm.getSpellingLoc(dloc), false).getFilename() << "." << std::endl;
                        /*FileManager& myFiles = sm.getFileManager();
                        const FileEntry *myFileEntry = myFiles.getFile(filename);
                        myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
                        Multi file support is WIP, disabled for now*/
                    }
                }
            }
        }
        return true;
    }
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
    MyASTConsumer(ASTContext *C) : FindingVisitor(C), ScanningVisitor(C), ModifyingVisitor(C), FinalizingVisitor(C) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        // Traversing the translation unit decl via a RecursiveASTVisitor
        // will visit all nodes in the AST.
        FindingVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        if(crits.empty() == false) {
            FindingVisitor.fixCrits(&Context);
        }
        std::cout << "Done finding.\n" << std::endl;
        ScanningVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        std::cout << "Done scanning.\n" << std::endl;
        ModifyingVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        ModifyingVisitor.AddStructs(false, false);
        //printCrits(&Context);
        ModifyingVisitor.TransformFunctions();
        printCrits(&Context);
        ModifyingVisitor.AddStructs(false, true);
        FinalizingVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        //printCrits(&Context);
    }

private:
    FindingASTVisitor FindingVisitor;
    ScanningASTVisitor ScanningVisitor;
    ModifyingASTVisitor ModifyingVisitor;
    FinalizingASTVisitor FinalizingVisitor;
};

using namespace llvm;

class MyASTClassAction : public clang::ASTFrontendAction {
private:
public:
    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
        auto r = std::unique_ptr<clang::ASTConsumer>(new MyASTConsumer(&Compiler.getASTContext()));
        return r;
    }
};

void printUsage() {
    std::cout << "\nUsage:\n\tqdtrans <single input file> [Clang options]\n\n";
}

/* Returns true if sr1 < sr2, false otherwise */
bool isSRLessThan(SourceRange sr1, SourceRange sr2, ASTContext* TheContext) {
    SourceManager& sm = TheContext->getSourceManager();
    FullSourceLoc fslend1 = FullSourceLoc(sr1.getEnd(), sm);
    unsigned end1 = std::get<1>(fslend1.getDecomposedLoc());
    FullSourceLoc fslstart2 = FullSourceLoc(sr2.getBegin(), sm);
    unsigned start2 = std::get<1>(fslstart2.getDecomposedLoc());
    if(start2 > end1) {
        return true;
    } else {
        return false;
    }
}

/* Returns true if sr1 is contained completely inside sr2, false otherwise */
bool isSRInside(SourceRange sr1, SourceRange sr2, ASTContext* TheContext) {
    SourceManager& sm = TheContext->getSourceManager();
    FullSourceLoc fslstart1 = FullSourceLoc(sr1.getBegin(), sm);
    FullSourceLoc fslend1 = FullSourceLoc(sr1.getEnd(), sm);
    unsigned start1 = std::get<1>(fslstart1.getDecomposedLoc());
    unsigned end1 = std::get<1>(fslend1.getDecomposedLoc());
    FullSourceLoc fslstart2 = FullSourceLoc(sr2.getBegin(), sm);
    FullSourceLoc fslend2 = FullSourceLoc(sr2.getEnd(), sm);
    unsigned start2 = std::get<1>(fslstart2.getDecomposedLoc());
    unsigned end2 = std::get<1>(fslend2.getDecomposedLoc());
    if(start1 > start2 && end1 < end2) {
        return true;
    } else {
        return false;
    }
}

Replacement createAdjustedReplacementForSR(SourceRange sr, ASTContext* TheContext, std::vector<Replacement>& repv, std::string text, bool injection, int newlength) {
    SourceManager& sm = TheContext->getSourceManager();
    FullSourceLoc fslstart = FullSourceLoc(sm.getFileLoc(sr.getBegin()), sm);
    FullSourceLoc fslend = FullSourceLoc(sm.getFileLoc(sr.getEnd()), sm);
    //FullSourceLoc gslstart = FullSourceLoc(sm.translateFileLineCol(sm.getFileEntryForID(sm.getMainFileID()), fslstart.getLine(), unsigned Col));
    //std::cerr << "\nDump:\n";
    unsigned start = sm.getFileOffset(fslstart);
    /*std::string string = sm.getFileEntryForID(sm.getFileID(fslstart))->getName().str();
    std::cout << "Text: " << text << std::endl;
    std::cout << "Start: Offset " << start << " in file " << string << "." << std::endl;*/
    unsigned length;
    if(newlength == 0) {
        if(injection == true) {
            length = 0;
        } else {
            length = sm.getFileOffset(fslend)-start;
        }
    } else {
        length = newlength;
    }
    unsigned adjstart = start;
    for(auto r : repv) {
        if(r.getOffset() <= adjstart) {
            //printf("adjstart = %u+%lu-%u\n", adjstart, r.getReplacementText().size(), r.getLength());
            adjstart = adjstart+r.getReplacementText().size()-r.getLength();
        }
    }
    //std::cout << "Start: " << start << ", End: " << start+length << std::endl;
    //std::cout << "AdjStart: " << adjstart << ", AdjEnd: " << adjstart+length << std::endl;
    Replacement newReplacement = Replacement(sm.getFileEntryForID(sm.getMainFileID())->getName(), start, length, StringRef(text));
    return newReplacement;
}

Replacement createInjectedReplacementForSR(SourceRange sr, ASTContext* TheContext, std::vector<Replacement>& repv, std::string text) {
    SourceManager& sm = TheContext->getSourceManager();
    Replacement newReplacement = Replacement(sm, sr.getBegin(), 0, StringRef(text));
    return newReplacement;    
}

/*Replacement createEndReplacement(ASTContext* TheContext, std::vector<Replacement>& repv, std::string text) {
    SourceManager& sm = TheContext->getSourceManager();
    //std::cout << "Start: " << start << ", End: " << start+length << std::endl;
    //std::cout << "AdjStart: " << adjstart << ", AdjEnd: " << adjstart+length << std::endl;
    Replacement newReplacement = Replacement(sm.getFileEntryForID(sm.getMainFileID())->getName(), sm.getFileEntryForID(sm.getMainFileID())->getSize()-1, 0, StringRef(text));
    return newReplacement;
}*/

void printCrits(ASTContext* TheContext) {
    std::cout << "[CRITSSTART]\n" << std::endl;
    struct criticalSection* c;
    for(unsigned i = 0; i < crits.size(); i++) {
        c = crits[i];
        std::string lfname = c->funcwlock->getNameInfo().getAsString();
        std::string ulfname = c->funcwunlock->getNameInfo().getAsString();
        std::cout << "Critical section " << i << " belonging to lock '" << c->lockname << "' detected, with length " << c->end-c->start << ", depth " << c->depth << ", lockdepth " << c->lockdepth << ", lockstatement '" << c->lockstmt << "' at position " << c->start << ", residing in function '" << lfname << "', and unlock statement '" << c->unlockstmt << "' at position " << c->end << ", residing in function '" << ulfname << "'." << std::endl;
        if(c->noMsgStruct == true) {
            std::cout << "Has no message struct." << std::endl;
        } else {
            std::cout << "Has a message struct." << std::endl;
        }
        std::cout << "noMsgStruct: " << c->noMsgStruct << std::endl;
        std::cout << "Contains the following variables:" << std::endl;
        for(auto v : *(c->accessedvars)) {
            std::string tloc;
            std::string ptr;
            std::string needsret;
            std::string array;
            if(v->threadLocal == true) {
                tloc = "True";
            } else {
                tloc = "False";
            }
            if(v->pointer == true) {
                ptr = "True";
            } else {
                ptr = "False";
            }
            if(v->needsReturn == true) {
                needsret = "True";
            } else {
                needsret = "False";
            }
            if(v->array == true) {
                array = "True";
            } else {
                array = "False";
            }
            std::cout << "    " << v->typestr << " " << v->namestr << " of locality '" << v->locality << "'.\n        threadLocal: " << tloc << ", pointer: " << ptr << ", needsReturn: " << needsret << ", array: " << array << "." << std::endl;
        }
        std::cout << "Has " << crits[i]->returnstmts->size() << " returns." << std::endl;
        for(auto r : *(c->returnstmts)) {
            PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
            PrintingPolicy& ppr = pp;
            std::string nodestring;
            llvm::raw_string_ostream os(nodestring);
            r->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
            SourceManager& sm = TheContext->getSourceManager();
            std::string locstring = r->getSourceRange().getBegin().printToString(sm);
            std::cout << locstring << "::" << os.str() << std::endl; 
        }
        std::cout << std::endl;
    }
    std::cout << "[CRITSEND]" << std::endl;
}

void deleteCrits() {
    for(unsigned c = 0; c < crits.size(); c++) {
        std::cout << "Deleting crit " << c << " at " << crits[c] << "..." << std::endl;
        for(unsigned i = 0; i < crits[c]->accessedvars->size(); i++) {
            std::cout << "    Deleting variable " << i << " at " << crits[c]->accessedvars->at(i) << "..." << std::endl;
            delete crits[c]->accessedvars->at(i);
        }
        delete crits[c]->accessedvars;
        delete crits[c]->unlockstmts;
        delete crits[c]->returnstmts;
        delete crits[c];
    }
}

long GetFileSize(std::string filename) {
    struct stat stat_buf;
    int rc = stat(filename.c_str(), &stat_buf);
    return rc == 0 ? stat_buf.st_size : -1;
}

// Apply a custom category to all command-line options so that they are the
// only ones displayed.
static llvm::cl::OptionCategory MyToolCategory("qdtrans options");

// CommonOptionsParser declares HelpMessage with a description of the common
// command-line options related to the compilation database and input files.
// It's nice to have this help message in all tools.
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

// A help message for this specific tool can be added afterwards.
static cl::extrahelp MoreHelp("\nUsage:\n\tqdtrans <single input file> [Clang options]\n\n");

int main(int argc, const char **argv) {
    // Ugly, ugly hack to fix an issue caused by the method used to inject new code in Clang (Clang runs off the end of its buffer at some point, injecting enough spaces at the end of the original file will hopefully give us the headroom we need.
    char* earlyfullpath = realpath(argv[1], NULL);
    std::string earlyname(earlyfullpath);
    std::string earlyname2 = earlyname.substr(0,earlyname.rfind('.')) + ".noqd.bak";
    std::stringstream cpcmd;
    cpcmd << "cp " << earlyname << " " << earlyname2;
    system(cpcmd.str().c_str());
    long filesize = GetFileSize(argv[1]);
    if(filesize == 0) {
        std::cout << "Input file is empty!" << std::endl;
        return 1;
    }
    //unsigned modsize = 0;
    std::string earlyline;
    std::vector<std::string> earlylines;
    /*std::ifstream earlyin(earlyfullpath);
    while (getline(earlyin,earlyline)) {
        std::cout << earlyline;
        earlylines.push_back(earlyline);
    }
    earlyin.close();*/
    std::ofstream earlyout;
    earlyout.open(earlyfullpath, std::ofstream::out | std::ofstream::app);
    for(int i = 0; i < filesize; i += 500) {
        earlyout << "                                                                                                                                                                                                                                                                                                                                                                                                                \n";
        //modsize += 1;
    }
    earlyout.close();
    free(earlyfullpath);
    // parse the command-line args passed to your code
    CommonOptionsParser op(argc, argv, MyToolCategory);
    // create a new Clang Tool instance (a LibTooling environment)
    RefactoringTool Tool(op.getCompilations(), op.getSourcePathList());
    const std::vector<std::string>& splistvec = op.getSourcePathList();
    /*std::cout << "[SPLISTSTART]" << std::endl;
    for(auto s : splistvec) {
        std::cout << s << std::endl;
        }*/
    std::string filename = splistvec[0];
    char* fullpath = realpath(filename.c_str(), NULL);
    filename = std::string(fullpath);
    //std::cout << "[SPLISTEND]" << std::endl;
    std::vector<std::string> args(argc-2);
    for(int i = 0; i < argc-2; i++) {
        args[i] = argv[i+2];
    }
    std::ifstream t(argv[1]);
    std::stringstream buffer;
    buffer << t.rdbuf();
    std::map<std::string, std::vector<Replacement>> rmap;
    RepMap = &rmap;
    //std::cout << RepMap << std::endl;
    std::vector<struct criticalSection*> criticalSections;
    crits = criticalSections;
    int result = Tool.run(newFrontendActionFactory<MyASTClassAction>().get());
    auto& myFiles = Tool.getFiles();
    
    /*DiagnosticOptions dopts;
    clang::DiagnosticIDs* DIDs = new clang::DiagnosticIDs();
    IntrusiveRefCntPtr<clang::DiagnosticIDs>* DiagID = new IntrusiveRefCntPtr<clang::DiagnosticIDs>(DIDs);
    TextDiagnosticPrinter *DiagClient = new clang::TextDiagnosticPrinter(llvm::errs(), &dopts, false);
    DiagnosticsEngine Diags(*DiagID, &dopts, DiagClient);*/
    clang::CompilerInstance CI;
    CI.createDiagnostics();
    SourceManager sm(CI.getDiagnostics(), myFiles, false);
    //std::cout << "FILENAME: " << "\"" << filename << "\"" << std::endl;
    const FileEntry *myFileEntry = myFiles.getFile(filename);
    
    LangOptions lopts;
    Rewriter Rw = Rewriter(sm, lopts);
    //sm.overrideFileContents(myFileEntry, myFileBuffer.get().get(), false);
    std::vector<Replacement> mainrepv = (*RepMap)[filename];
    std::cout << "[REPSSTART]\n";
    /*auto*/const RewriteBuffer * myFileBuffer;
    bool started = false;
    //std::sort(mainrepv.begin(), mainrepv.end());
    for(auto r : mainrepv) {
        if(started == true) {
            //myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
            //std::cout << "Size: " << myFileBuffer->size() << "." << std::endl;
        } else {
            started = true;
        }
        std::cout << r.toString() << "\n" << r.getFilePath().str() << std::endl;
        std::cout << "Offset: " << r.getOffset() << std::endl;
        r.apply(Rw);
        /*myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
        llvm::outs() << "[BUFSTART:" << myFileBuffer->size() << "]\n";
        
        myFileBuffer->write(llvm::outs());
        llvm::outs() << "[BUFEND]\n";*/
    }
    std::cout << "[REPSEND]\n";
    /*auto myFileBuffer = myFiles.getBufferForFile(filename);
    if(!myFileBuffer) {
        std::cerr << "Nope" << std::endl;
        }*/
    myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
    //llvm::outs() << "[BUFSTART]\n";
    //myFileBuffer->write(llvm::outs());
    //llvm::outs() << "[BUFEND]\n";
    std::string filename2 = filename.substr(0,filename.rfind('.')) + ".noqd.bak";
    std::string filename3 = filename.substr(0,filename.rfind('.')) + ".qd.c";
    std::string cmdcppstr;
    std::stringstream cmd(cmdcppstr);
    cmd << "cp " << filename << " " << filename2;
    //system(cmdcppstr.str().c_str());
    std::cout << "Saving to " << filename << " (original code backed up to "<< filename2 << ")...\n" << std::endl;
    //std::cout << "Filename: " << filename << "." << std::endl;
    unsigned critcount = 0;
    unsigned transformed = 0;
    unsigned acrits = 0;
    unsigned bcrits = 0;
    unsigned ccrits = 0;
    for(unsigned i = 0; i < crits.size(); i++) {
        critcount++;
        if(crits[i]->transformed == true) {
            transformed++;
        }
        switch(crits[i]->type) {
        case 'A':
            acrits++;
            break;
        case 'B':
            bcrits++;
            break;
        case 'C':
            ccrits++;
            break;
        default:
            std::cout << "Invalid crit type detected, please debug and fix this." << std::endl;
        };
    }
    std::cout << "Critical sections counted: " << critcount << std::endl;
    std::cout << "Successfully transformed: " << transformed << std::endl;
    std::cout << "Type A: " << acrits << std::endl;
    std::cout << "Type B: " << bcrits << std::endl;
    std::cout << "Type C: " << ccrits << std::endl;
    std::error_code error;
    llvm::sys::fs::OpenFlags of = llvm::sys::fs::F_None;
    raw_fd_ostream rfod(StringRef(filename), error, of);
    raw_fd_ostream rfod2(StringRef(filename3), error, of);
    //std::cout << "Got buffer for filename " << filename << "." << std::endl;
    //std::cout << "Could have been " << argv[1] << "." << std::endl;
    //std::cout << error << std::endl;
    myFileBuffer->write(rfod);
    myFileBuffer->write(rfod2);
    //myFiles.PrintStats();
    free(fullpath);
    deleteCrits();
    return result;
}
