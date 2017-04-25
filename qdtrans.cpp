#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>

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

#include "clang/AST/ODRHash.h"

typedef int* intptr;

enum locality {UNDEF, GLOBAL, CRITLOCAL, ELSELOCAL}; // GLOBAL = global, CRITLOCAL = declared inside its critical section, ELSELOCAL = declared non-globally but outside its critical section.

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
    std::vector<struct variable*> accessedvars;
    signed depth;
    clang::Stmt* lockstmt;
    clang::Stmt* unlockstmt;
};

using namespace clang;
using namespace clang::tooling;

std::map<std::string, std::vector<Replacement>>* RepMap;
std::vector<struct criticalSection*> crits;

Stmt* thestmt;

Replacement createAdjustedReplacementForSR(SourceRange sr, ASTContext* TheContext, std::vector<Replacement>& repv, std::string text, bool injection, int newlength);

/* Returns true if sr1 < sr2, false otherwise */
bool isSRLessThan(SourceRange sr1, SourceRange sr2, ASTContext* TheContext);

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class FindingASTVisitor : public RecursiveASTVisitor<FindingASTVisitor> {
private:
    ASTContext *TheContext;
public:
    FindingASTVisitor(ASTContext *C) : TheContext(C) {
        //LastContext = TheContext;
        std::vector<Replacement> vec;
        (*RepMap)[TheContext->getSourceManager().getFileEntryForID(TheContext->getSourceManager().getMainFileID())->getName()] = vec; //Initializing the Replacement vector
        SourceManager& sm = TheContext->getSourceManager();
        StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
        std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
        Replacement newReplacement = Replacement(sm.getFileEntryForID(sm.getMainFileID())->getName(), 0, 0, "");
        maprepv.push_back(newReplacement); //Adding dummy replacement to prent crash when attempting o get unmodified buffer.
        (*RepMap)[filename.str()] = maprepv;
    }

    void checkStatement(Stmt* stmt, struct criticalSection** newcrit, bool* inCrit, bool* needspush, bool* skip, unsigned depth, llvm::raw_string_ostream& os, std::string& nodestring, std::stringstream& nodetext) {
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
                        nodetext.str("");
                        nodestring = "";
                        (*newcrit) = new criticalSection;
                        (*newcrit)->accessedvars = *(new std::vector<struct variable*>);
                        (*newcrit)->lockstmt = stmt;
                        (*newcrit)->depth = depth;
                        PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                        PrintingPolicy& ppr = pp;
                        MyCallExpr->getArg(0)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                        (*newcrit)->lockname = os.str();
                        std::cout << "New lock has lockname \"" << (*newcrit)->lockname << "\"." << std::endl;
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
                        std::cout << "Comparing \"" << lname << "\" and \"" << (*newcrit)->lockname << "\"." << std::endl;
                        if(lname.compare((*newcrit)->lockname) == 0) {
                            (*newcrit)->unlockstmt = stmt;
                            (*newcrit)->depth = depth-(*newcrit)->depth;
                        }
                    } else if(name == "pthread_mutex_lock") {
                        crits.push_back((*newcrit));
                        //std::cout << "Pushed!" << std::endl;
                        *inCrit = false;
                        *needspush = false;
                        *skip = true;
                    }
                } 
            } 
        }
    }
    
    void checkStatements(Stmt* stmt, struct criticalSection** newcrit, bool* inCrit, bool* needspush, bool* skip, unsigned depth, llvm::raw_string_ostream& os, std::string& nodestring, std::stringstream& nodetext) {
        Stmt::child_iterator ChildIterator = stmt->child_begin();
        bool needspushlocal = false;
        while(ChildIterator != stmt->child_end()) {
            if(*ChildIterator != NULL) {
                std::cout << "Depth: " << depth << ", type: " << stmt->getStmtClassName() << ", inCrit: " << *inCrit << std::endl;
                checkStatement(*ChildIterator, newcrit, inCrit, &needspushlocal, skip, depth, os, nodestring, nodetext);
            }
            //std::cout << "needspush: " << needspush << std::endl;
            if(*skip == false) {
                checkStatements(*ChildIterator, newcrit, inCrit, NULL, skip, depth+1, os, nodestring, nodetext);
                ChildIterator++;
            } else {
                *skip = false;
            }
        }
        if(needspushlocal == true) {
            crits.push_back((*newcrit));
            std::cout << "Pushed!" << std::endl;
            needspushlocal = false;
        }
    }

    bool VisitDecl(Decl *d) {
        if(isa<TranslationUnitDecl>(d)) {
            d->dumpColor();
            TranslationUnitDecl* tud = cast<TranslationUnitDecl>(d);
            DeclContext::decl_iterator DeclIterator = tud->decls_begin();
            int i = 0;
            bool inCrit = false;
            bool skip = false;
            std::stringstream nodetext;
            std::string nodestring;
            llvm::raw_string_ostream os(nodestring);
            struct criticalSection* newcrit = NULL;
            //bool needspush = false;
            while(DeclIterator != tud->decls_end()) {
                if(isa<FunctionDecl>(*DeclIterator)) {
                    //std::cout << "Func: " << i << std::endl;
                    //(*DeclIterator)->dumpColor();
                    FunctionDecl* funcdecl = cast<FunctionDecl>(*DeclIterator);
                    Stmt* funcbody = funcdecl->getBody();
                    if(funcbody != NULL) {
                        checkStatements(funcbody, &newcrit, &inCrit, NULL, &skip, 0, os, nodestring, nodetext);
                    }
                    i++;
                }
                DeclIterator++;
            }
        }
        return true;
    }
};

class ScanningASTVisitor : public RecursiveASTVisitor<ScanningASTVisitor> {
private:
    ASTContext *TheContext;
    TranslationUnitDecl* TheTUD;
public:
    ScanningASTVisitor(ASTContext *C) : TheContext(C) {}

    bool VisitExpr(Expr *e) {
        if(isa<DeclRefExpr>(e)) {
            for(auto c : crits) {
                if((isSRLessThan(c->lockstmt->getSourceRange(), e->getSourceRange(), TheContext) == true) && (isSRLessThan(e->getSourceRange(), c->unlockstmt->getSourceRange(), TheContext) == true)) {
                    //if(isa<FunctionDecl>(e->)
                    DeclarationNameInfo declname = ((DeclRefExpr*)(e))->getNameInfo();
                    std::string name = declname.getName().getAsString();
                    bool dup = false;
                    for(auto v : c->accessedvars) {
                        if(v->namestr.compare(name) == 0) {
                            dup = true;
                        }
                    }
                    std::string tstr = ((DeclRefExpr*)(e))->getDecl()->getType().getAsString();
                    const char* tstring = tstr.c_str();
                    if((dup == false) && (isa<FunctionDecl>(((DeclRefExpr*)(e))->getDecl()) == false)) {
                        struct variable* newvar = new struct variable;
                        newvar->namestr = name;
                        std::cout << "Name: " << name << std::endl;
                        newvar->typestr = tstr;
                        //newvar->typestr = declname.getNamedTypeInfo()->getType().getAsString();
                        std::cout << "Type: " << newvar->typestr << std::endl;
			if(strstr(tstring, "*") != NULL) {
			    newvar->pointer = true;
			} else {
			    newvar->pointer = false;
			}
                        Decl* d = ((DeclRefExpr*)(e))->getDecl();
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
                                newvar->locality = ELSELOCAL;
                                newvar->needsReturn = true;
                            }
                        }
                        c->accessedvars.push_back(newvar);
                    }
                }
            }
        }
        return true;
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
            if((SRset == false) || (isSRLessThan(d->getSourceRange(), SRToAddTo, TheContext) == true)) {
                SRToAddTo = d->getSourceRange();
                SRset = true;
            }
        }
        return true;
    }

    void AddStructs(bool addEmptyStructs) {
        std::cout << "Adding structs..." << std::endl;
        for(unsigned i = 0; i < crits.size(); i++) {
            std::stringstream nodetext;
            nodetext << "struct critSec" << i << "_msg {\n";
            unsigned varcount = 0;
            for(unsigned v = 0; v < crits[i]->accessedvars.size(); v++) {
                if(crits[i]->accessedvars[v]->locality == ELSELOCAL) {
                    nodetext << "    " << crits[i]->accessedvars[v]->typestr << " " << crits[i]->accessedvars[v]->namestr << "\n";
                }
            }
            nodetext << "\n};\n\n";
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
        }
    }
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
    MyASTConsumer(ASTContext *C) : FindingVisitor(C), ScanningVisitor(C), ModifyingVisitor(C) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        // Traversing the translation unit decl via a RecursiveASTVisitor
        // will visit all nodes in the AST.
        FindingVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        std::cout << "Done finding.\n" << std::endl;
        ScanningVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        std::cout << "Done scanning.\n" << std::endl;
        ModifyingVisitor.TraverseDecl(Context.getTranslationUnitDecl());
        ModifyingVisitor.AddStructs(false);
    }

private:
    FindingASTVisitor FindingVisitor;
    ScanningASTVisitor ScanningVisitor;
    ModifyingASTVisitor ModifyingVisitor;
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
            printf("adjstart = %u+%lu-%u\n", adjstart, r.getReplacementText().size(), r.getLength());
            adjstart = adjstart+r.getReplacementText().size()-r.getLength();
        }
    }
    std::cout << "Start: " << start << ", End: " << start+length << std::endl;
    std::cout << "AdjStart: " << adjstart << ", AdjEnd: " << adjstart+length << std::endl;
    Replacement newReplacement = Replacement(sm.getFileEntryForID(sm.getMainFileID())->getName(), start, length, StringRef(text));
    return newReplacement;
}

void printCrits() {
    std::cout << "[CRITSSTART]" << std::endl;
    for(auto c : crits) {
        std::cout << "Critical section belonging to lock '" << c->lockname << "' detected, with depth " << c->depth << ", lockstatement '" << c->lockstmt << "' and unlock statement '" << c->unlockstmt << std::endl;
        if(c->noMsgStruct == true) {
            std::cout << "Has no message struct." << std::endl;
        } else {
            std::cout << "Has a message struct." << std::endl;
        }
        std::cout << "Contains the following variables:" << std::endl;
        for(auto v : c->accessedvars) {
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
            std::cout << "    " << v->typestr << v->namestr << " of locality '" << v->locality << "'.\n        threadLocal: " << tloc << ", pointer: " << ptr << ", needsReturn: " << needsret << "." << std::endl;
        }
    }
    std::cout << "[CRITSEND]" << std::endl;
}

void deleteCrits() {
    for(auto c : crits) {
        for(auto v : c->accessedvars) {
            delete v;
        }
        //delete c->accessedvars;
        delete c;
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
    std::cout << "[SPLISTSTART]" << std::endl;
    for(auto s : splistvec) {
        std::cout << s << std::endl;
    }
    std::string filename = splistvec[0];
    std::cout << "[SPLISTEND]" << std::endl;
    std::vector<std::string> args(argc-2);
    for(int i = 0; i < argc-2; i++) {
        args[i] = argv[i+2];
    }
    std::ifstream t(argv[1]);
    std::stringstream buffer;
    buffer << t.rdbuf();
    std::map<std::string, std::vector<Replacement>> rmap;
    RepMap = &rmap;
    std::cout << RepMap << std::endl;
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
    std::cout << "FILENAME: " << "\"" << filename << "\"" << std::endl;
    const FileEntry *myFileEntry = myFiles.getFile(filename);
    
    LangOptions lopts;
    Rewriter Rw = Rewriter(sm, lopts);
    //sm.overrideFileContents(myFileEntry, myFileBuffer.get().get(), false);
    printCrits();
    std::vector<Replacement> mainrepv = (*RepMap)[filename];
    llvm::outs() << "[REPSSTART]\n";
    for(auto r : mainrepv) {
        std::cout << r.toString() << std::endl;
        r.apply(Rw);
        /*auto myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
        llvm::outs() << "[BUFSTART:" << myFileBuffer->size() << "]\n";
        
        myFileBuffer->write(llvm::outs());*/
        llvm::outs() << "[BUFEND]\n";
    }
    llvm::outs() << "[REPSEND]\n";
    /*auto myFileBuffer = myFiles.getBufferForFile(filename);
    if(!myFileBuffer) {
        std::cerr << "Nope" << std::endl;
        }*/
    auto myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
    llvm::outs() << "[BUFSTART]\n";
    myFileBuffer->write(llvm::outs());
    llvm::outs() << "[BUFEND]\n";
    myFiles.PrintStats();
    deleteCrits();
    return result;
}
