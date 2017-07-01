#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <system_error>

#include <limits.h>

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

unsigned critcount = 0;
unsigned transformed = 0;
unsigned acrits = 0;
unsigned bcrits = 0;
unsigned ccrits = 0;

Replacement createAdjustedReplacementForSR(SourceRange sr, ASTContext* TheContext, std::vector<Replacement>& repv, std::string text, bool injection, int newlength);

/* Returns true if sr1 < sr2, false otherwise */
bool isSRLessThan(SourceRange sr1, SourceRange sr2, ASTContext* TheContext);

/* Returns true if sr1 is contained completely inside sr2, false otherwise */
bool isSRInside(SourceRange sr1, SourceRange sr2, ASTContext* TheContext);

void printCrits();

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
                        //std::cout << "Found!" << std::endl;
                        *inCrit = true;
                        *needspush = true;
                        //std::cout << "Setting needspush (is " << *needspush << ", could be " << needspush << ")..." << std::endl;
                        nodetext.str("");
                        nodestring = "";
                        (*newcrit) = new criticalSection;
                        (*newcrit)->accessedvars = (new std::vector<struct variable*>);
                        (*newcrit)->lockstmt = stmt;
                        (*newcrit)->unlockstmt = NULL;
                        (*newcrit)->funcwlock = fdecl;
                        (*newcrit)->lockdepth = depth-fdepth;
                        (*newcrit)->depth = depth;
                        (*newcrit)->needsWait = false;
                        (*newcrit)->stmtabovelock = stmt2;
                        (*newcrit)->typeA = true;
                        (*newcrit)->start = std::get<1>(FullSourceLoc(stmt->getLocStart(), TheContext->getSourceManager()).getDecomposedLoc());
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
                        PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                        PrintingPolicy& ppr = pp;
                        nodestring = "";
                        MyCallExpr->getArg(0)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                        std::string lname = os.str();
                        //std::cout << "Comparing \"" << lname << "\" and \"" << (*newcrit)->lockname << "\"." << std::endl;
                        if(lname.compare((*newcrit)->lockname) == 0) {
                            (*newcrit)->unlockstmt = stmt;
                            (*newcrit)->funcwunlock = fdecl;
                            (*newcrit)->depth = depth-(*newcrit)->depth;
                            if((*newcrit)->typeA == true) {
                                if((*newcrit)->stmtabovelock != stmt2) {
                                    (*newcrit)->typeA = false;
                                }
                            }
                            (*newcrit)->end = std::get<1>(FullSourceLoc(stmt->getLocEnd(), TheContext->getSourceManager()).getDecomposedLoc());
                        }
                    } else if(name == "pthread_mutex_lock") {
                        if((*newcrit)->unlockstmt != NULL) {
                            crits.push_back((*newcrit));
                            //std::cout << "169 pushed " << (*newcrit) << "." << std::endl;
                            critcount++;
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
            } 
        }
    }
    
    void checkStatements(Stmt* stmt, struct criticalSection** newcrit, bool* inCrit, bool* needspush, bool* skip, unsigned depth, llvm::raw_string_ostream& os, std::string& nodestring, std::stringstream& nodetext, std::vector<FunctionDecl*>* fstack) {
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
                    fstack->push_back(fdecl);
                    checkStatements(fdecl->getBody(), newcrit, inCrit, needspush, skip, depth+1, os, nodestring, nodetext, fstack);
                    fstack->pop_back();
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
                    checkStatements(*ChildIterator, newcrit, inCrit, needspush, skip, depth+1, os, nodestring, nodetext, fstack);
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
            while(DeclIterator != tud->decls_end()) {
                if(isa<FunctionDecl>(*DeclIterator)) {
                    //std::cout << "Func: " << i << std::endl;
                    //(*DeclIterator)->dumpColor();
                    FunctionDecl* funcdecl = cast<FunctionDecl>(*DeclIterator);
                    Stmt* funcbody = funcdecl->getBody();
                    if(funcbody != NULL) {
                        std::string fname = funcdecl->getNameInfo().getAsString();
                        fstack.push_back(funcdecl);
                        checkStatements(funcbody, &newcrit, &inCrit, &needspush, &skip, 0, os, nodestring, nodetext, &fstack);
                        //std::cout << "Checking needspush (is " << needspush << ")..." << std::endl;
                        if(needspush == true) {
                            crits.push_back(newcrit);
                            //std::cout << "255 Pushed " << newcrit << "." << std::endl;
                            critcount++;
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

    void fixCrits() { // Crude fix for crits sometimes having invalid (NULL) unlock statements because pushing to repvec is flaky. Also removes duplicate crits.
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
            std::string name;
            std::string tstr;
            clang::DeclStmt::decl_iterator DeclIterator;
            Decl* d;
            if(isa<DeclRefExpr>(s)) {
                dre = true;
                Expr* e = cast<Expr>(s);
                DeclarationNameInfo declname = ((DeclRefExpr*)(e))->getNameInfo();
                name = declname.getName().getAsString();
                tstr = ((DeclRefExpr*)(e))->getDecl()->getType().getAsString();
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
                            if(isa<VarDecl>(d)) {
                                name = cast<VarDecl>(d)->getNameAsString();
                                tstr = cast<ValueDecl>(d)->getType().getAsString();
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
                        if((sm.getPresumedLoc(sm.getSpellingLoc(sloc), false).getFilename() == sm.getFileEntryForID(sm.getMainFileID())->getName()) && (FullSourceLoc(sloc, sm).isBeforeInTranslationUnitThan(c->unlockstmt->getLocStart()) == true && FullSourceLoc(c->lockstmt->getLocStart(), sm).isBeforeInTranslationUnitThan(sloc)) == true) {
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
                                //newvar->typestr = declname.getNamedTypeInfo()->getType().getAsString();
                                //std::cout << "Type: " << newvar->typestr << std::endl;
                                if(strstr(tstring, "*") != NULL) {
                                    newvar->pointer = true;
                                } else {
                                    newvar->pointer = false;
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
                                            newvar->needsReturn = true;
                                        }
                                    }
                                }
                                if(newvar->locality == CRITLOCAL || newvar->locality == FUNLOCAL) {
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
    SourceRange SRToAddTo;
    bool SRset = false;
public:
    ModifyingASTVisitor(ASTContext *C) : TheContext(C) {}

    bool VisitDecl(Decl *d) {
        if(isa<FunctionDecl>(d)) {
            SourceManager& sm = TheContext->getSourceManager();
            if(((SRset == false) || (isSRLessThan(d->getSourceRange(), SRToAddTo, TheContext) == true)) && sm.getPresumedLoc(sm.getSpellingLoc(d->getLocation()), false).getFilename() == sm.getFileEntryForID(sm.getMainFileID())->getName()) {
                SRToAddTo = d->getSourceRange();
                SRset = true;
            }
        }
        return true;
    }

    void AddStructs(bool addEmptyStructs, bool addStructs) {
        std::cout << "Adding structs..." << std::endl;
        for(unsigned i = 0; i < crits.size(); i++) {
            std::stringstream nodetext;
            std::string lfname = crits[i]->funcwlock->getNameInfo().getAsString();
            nodetext << "struct " << lfname << "_critSec" << i << "_msg {\n";
            unsigned varcount = 0;
            for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                if(((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL) || ((*(crits[i]->accessedvars))[v]->locality == FUNLOCAL) || (((*(crits[i]->accessedvars))[v]->locality == CRITLOCAL) && ((*(crits[i]->accessedvars))[v]->needsReturn == true))) {
                    nodetext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " " << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    varcount++;
                }
            }
            nodetext << "};\n\n";
            if(addStructs == true) {
                if(varcount > 0 || addEmptyStructs == true) {
                    crits[i]->noMsgStruct = false;
                    SourceManager& sm = TheContext->getSourceManager();
                    StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                    std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                    Replacement rep = createAdjustedReplacementForSR(SRToAddTo, TheContext, maprepv, nodetext.str(), true, 0);
                    maprepv.push_back(rep);
                    (*RepMap)[filename.str()] = maprepv;
                } else {
                    crits[i]->noMsgStruct = true;
                }
            } else {
                if(varcount > 0 || addEmptyStructs == true) {
                    std::cout << "Critical section " << i << " has a message struct." << std::endl;
                    crits[i]->noMsgStruct = false;
                    std::cout << "noMsgStruct: " << crits[i]->noMsgStruct << std::endl;
                } else {
                    std::cout << "Critical section " << i << " has no message struct." << std::endl;
                    crits[i]->noMsgStruct = true;
                    std::cout << "noMsgStruct: " << crits[i]->noMsgStruct << std::endl;
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
            Replacement deleterep;
            Replacement firstrep;
            std::string structname;
            std::string lfname = crits[i]->funcwlock->getNameInfo().getAsString();
            if(crits[i]->noMsgStruct == false) {
                std::stringstream sns;
                sns << lfname << "_cs" << i << "msg";
                structname = sns.str();
                nodetext << "struct " << lfname << "_critSec" << i << "_msg " << structname << ";\n";
                for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                    if((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL || (*(crits[i]->accessedvars))[v]->locality == FUNLOCAL) {
                        nodetext << "    " << structname << "." << (*(crits[i]->accessedvars))[v]->namestr << " = " << (*(crits[i]->accessedvars))[v]->namestr << ";\n\n";
                    }
                }
            }
            functext << "void " << lfname << "_critSec" << i << "(unsigned int sz, void* msgP) {\n";
            if(crits[i]->noMsgStruct == false) {
                functext << "    struct " << lfname << "_critSec" << i << "_msg* " << lfname << "_cs" << i << "msg = (struct critSec" << i << "_msg*)msgP;\n";
                for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                    if((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL || (*(crits[i]->accessedvars))[v]->locality == FUNLOCAL) {
                        functext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " " << (*(crits[i]->accessedvars))[v]->namestr << " = " << structname << "->" << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    }
                }
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
            if(crits[i]->needsWait == true) {
                nodetext << "LL_delegate_wait(";
            } else {
                nodetext << "LL_delegate(";
            }
            nodetext << crits[i]->lockname << ", " << lfname << "_critSec" << i;
            if(crits[i]->noMsgStruct == false) {
                nodetext << ", sizeof(" << structname << "), &" << structname << ");\n";
                for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                    if(((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL || (*(crits[i]->accessedvars))[v]->locality == FUNLOCAL) && (*(crits[i]->accessedvars))[v]->needsReturn == true) {
                        nodetext << "    " << (*(crits[i]->accessedvars))[v]->namestr << " = " << lfname << "_cs" << i << "msg." << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    } else if((*(crits[i]->accessedvars))[v]->locality == CRITLOCAL && (*(crits[i]->accessedvars))[v]->needsReturn == true) {
                        nodetext << "    " << (*(crits[i]->accessedvars))[v]->typestr << " " << (*(crits[i]->accessedvars))[v]->namestr << " = " << lfname << "_cs" << i << "msg." << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
                    }
                }
            } else {
                nodetext << ", 0, NULL);\n";
            }
            nodetext << "    ";
            bool first = true;
            //std::cout << "Checking..." << std::endl;
            if(crits[i]->depth == 0 && crits[i]->typeA == true) {
                topBody = crits[i]->stmtabovelock;
                topIterator = topBody->child_begin();
                currBody = topBody;
                currIterator = topIterator;
                //std::cout << "Checked, case 1." << std::endl;
                transformed++;
                acrits++;
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
                    bool isUnlock = false;
                    if(isa<CallExpr>(*topIterator)) {
                        CallExpr* MyCallExpr = cast<CallExpr>(*topIterator);
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
                    (*topIterator)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                    if(isUnlock == false) {
                        functext << "    " << os.str() << ";\n";
                    }
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
                    transformed--;
                    critcount--;
                    acrits--;
                } else {
                    if(crits[i]->noMsgStruct == false) {
                        for(unsigned v = 0; v < crits[i]->accessedvars->size(); v++) {
                            if(((*(crits[i]->accessedvars))[v]->locality == ELSELOCAL || (*(crits[i]->accessedvars))[v]->locality == FUNLOCAL || (*(crits[i]->accessedvars))[v]->locality == CRITLOCAL) && (*(crits[i]->accessedvars))[v]->needsReturn == true) {
                                functext << "    " << structname << "->" << (*(crits[i]->accessedvars))[v]->namestr << " = " << (*(crits[i]->accessedvars))[v]->namestr << ";\n";
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
                    Replacement funcrep = createAdjustedReplacementForSR(SRToAddTo, TheContext, maprepv, functext.str(), true, 0);
                    maprepv.push_back(funcrep);
                    maprepv.push_back(deleterep);
                    maprepv.push_back(firstrep);
                    //std::cout << "Pushed to " << filename.str() << "." << std::endl;
                    (*RepMap)[filename.str()] = maprepv;
                }
            } else if(crits[i]->funcwlock == crits[i]->funcwunlock) { // For counting mechanism
                bcrits++;
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
                ccrits++;
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
                if(name == "pthread_mutex_init" || name == "pthread_mutex_destroy") {
                    std::string nodestring;
                    llvm::raw_string_ostream os(nodestring);
                    PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                    PrintingPolicy& ppr = pp;
                    MyCallExpr->getArg(0)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                    std::string lname = os.str();
                    bool isQD = false;
                    for(unsigned c = 0; c < crits.size(); c++) {
                        if(lname.compare(crits[c]->lockname) == 0) {
                            isQD = true;
                            break;
                        }
                    }
                    if(isQD == true) {
                        std::stringstream newnode;
                        unsigned length;
                        if(name == "pthread_mutex_init") {
                            newnode << "LL_initialize(" << lname << ");\n";
                            length = 28+lname.length();
                        } else {
                            //newnode << "LL_destroy(" << lname << ");\n";
                            newnode << ""; // Fix for weird issue, shouldn't matter since LL_destroy doesn't actually do anything.
                            length = 25+lname.length();
                        }
                        //e->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                        SourceManager& sm = TheContext->getSourceManager();
                        StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                        std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                        Replacement rep = createAdjustedReplacementForSR(e->getSourceRange(), TheContext, maprepv, newnode.str(), true, length);
                        maprepv.push_back(rep);
                        (*RepMap)[filename.str()] = maprepv;
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
            FindingVisitor.fixCrits();
        }
        std::cout << "Done finding.\n" << std::endl;
        ScanningVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        std::cout << "Done scanning.\n" << std::endl;
        ModifyingVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        ModifyingVisitor.AddStructs(false, false);
        printCrits();
        ModifyingVisitor.TransformFunctions();
        ModifyingVisitor.AddStructs(false, true);
        FinalizingVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        //printCrits();
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
    FullSourceLoc fslstart = FullSourceLoc(sr.getBegin(), sm);
    FullSourceLoc fslend = FullSourceLoc(sr.getEnd(), sm);
    unsigned start = std::get<1>(fslstart.getDecomposedLoc());
    unsigned length;
    if(newlength == 0) {
        if(injection == true) {
            length = 0;
        } else {
            length = std::get<1>(fslend.getDecomposedLoc())-start;
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

void printCrits() {
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
            std::cout << "    " << v->typestr << " " << v->namestr << " of locality '" << v->locality << "'.\n        threadLocal: " << tloc << ", pointer: " << ptr << ", needsReturn: " << needsret << "." << std::endl;
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
        delete crits[c];
    }
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
    int intorz = 73;
    intptr ip = &intorz;
    ip++;
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
    //llvm::outs() << "[REPSSTART]\n";
    /*auto*/const RewriteBuffer * myFileBuffer;
    bool started = false;
    for(auto r : mainrepv) {
        if(started == true) {
            //myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
            //std::cout << "Size: " << myFileBuffer->size() << "." << std::endl;
        } else {
            started = true;
        }
        //std::cout << r.toString() << std::endl;
        r.apply(Rw);
        /*auto myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
        llvm::outs() << "[BUFSTART:" << myFileBuffer->size() << "]\n";
        
        myFileBuffer->write(llvm::outs());*/
        //llvm::outs() << "[BUFEND]\n";
    }
    //llvm::outs() << "[REPSEND]\n";
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
    system(cmd.str().c_str());
    std::cout << "Saving to " << filename << " (original code backed up to "<< filename2 << ")...\n" << std::endl;
    //std::cout << "Filename: " << filename << "." << std::endl;
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
    //return result;
    return 0;
}



