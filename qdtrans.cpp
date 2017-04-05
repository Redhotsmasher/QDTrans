//------------------------------------------------------------------------------
// Clang rewriter sample. Demonstrates:
//
// * How to use RecursiveASTVisitor to find interesting AST nodes.
// * How to use the Rewriter API to rewrite the source code.
//
// Eli Bendersky (eliben@gmail.com)
// This code is in the public domain
//------------------------------------------------------------------------------
#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
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

using namespace clang;
using namespace clang::tooling;

std::map<std::string, std::vector<Replacement>>* RepMap;

Replacement createAdjustedReplacementForSR(SourceRange sr, ASTContext* TheContext, std::vector<Replacement>& repv, std::string text, bool injection, int newlength);

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
private:
    ASTContext *TheContext;
    //Rewriter &TheRewriter;
    //Replacements &TheReplacements;
public:
    MyASTVisitor(ASTContext *C) : TheContext(C) {
        //LastContext = TheContext;
        std::vector<Replacement> vec;
        (*RepMap)[TheContext->getSourceManager().getFileEntryForID(TheContext->getSourceManager().getMainFileID())->getName()] = vec; //Initializing the Replacement vector
        /*SourceManager& sm = TheContext->getSourceManager();
        StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
        std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
        Replacement newReplacement = Replacement(sm.getFileEntryForID(sm.getMainFileID())->getName(), 0, 0, "");
        maprepv.push_back(newReplacement);
        (*RepMap)[filename.str()] = maprepv;*/
    }

    bool VisitStmt(Stmt *s) {
        Stmt::child_iterator ChildIterator = s->child_begin();
        SourceRange SRToAddTo;
        bool inCrit = false;
        std::stringstream nodetext;
        std::string nodestring;
        llvm::raw_string_ostream os(nodestring);
        while(ChildIterator != s->child_end()) {
            if(inCrit == false) {
                if(isa<CallExpr>(*ChildIterator)) {
                    CallExpr* MyCallExpr = cast<CallExpr>(*ChildIterator);
                    FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                    if(MyFunDecl != 0) {
                        std::string name = MyFunDecl->getNameInfo().getName().getAsString();
                        if(ChildIterator != s->child_end() && name == "pthread_mutex_lock") {
                            SourceRange sr = (*ChildIterator)->getSourceRange();
                            SRToAddTo = SourceRange(sr.getBegin(), sr.getEnd());
                            inCrit = true;
                            nodetext.str("");
                            nodestring = "";
                        }
                    }
                } 
            } else {
                bool goelse = false;
                if(isa<CallExpr>(*ChildIterator)) {
                    CallExpr* MyCallExpr = cast<CallExpr>(*ChildIterator);
                    FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                    if(MyFunDecl != 0) {
                        std::string name = MyFunDecl->getNameInfo().getName().getAsString();
                        if(ChildIterator != s->child_end() && name == "pthread_mutex_unlock") {
                            SourceManager& sm = TheContext->getSourceManager();
                            StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                            std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                            Replacement rep = createAdjustedReplacementForSR(SRToAddTo, TheContext, maprepv, nodetext.str(), true, 0);
                            maprepv.push_back(rep);
                            std::cout << rep.toString() << std::endl;
                            (*RepMap)[filename.str()] = maprepv;
                    //maprepv.push_back(rep);
                            inCrit = false;
                        } else {
                            goelse = true;
                        }
                    } else {
                        goelse = true;
                    }
                } else {
                    goelse = true;
                }
                if(goelse == true) { //Deduplicated else section starts here
                    nodestring = "";
                    PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                    PrintingPolicy& ppr = pp;
                    llvm::outs() << "NODE:\n";
                    (*ChildIterator)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                    SourceRange sr = (*ChildIterator)->getSourceRange();
                    SourceManager& sm = TheContext->getSourceManager();
                    StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                    std::vector<Replacement> maprepv = (*RepMap)[filename.str()];
                    nodetext << os.str() << ";\n";
                    Replacement rep2 = createAdjustedReplacementForSR(sr, TheContext, maprepv, "", false, nodestring.length()+2);
                    std::cout << rep2.toString() << std::endl;
                    maprepv.push_back(rep2);
                    (*RepMap)[filename.str()] = maprepv;
                }
            }
            ChildIterator++;
        } 
        return true;
    }
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
    MyASTConsumer(ASTContext *C) : Visitor(C) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
  virtual void HandleTranslationUnit(clang::ASTContext &Context) {
    // Traversing the translation unit decl via a RecursiveASTVisitor
    // will visit all nodes in the AST.
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
  }

private:
  MyASTVisitor Visitor;
};

using namespace llvm;

class MyASTClassAction : public clang::ASTFrontendAction {
private:
    //Replacements &TheReplacements;
    //Rewriter TheRewriter;
    //std::string TheCode;
public:
    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
        //Rewriter &RwRef = Rw;
        auto r = std::unique_ptr<clang::ASTConsumer>(new MyASTConsumer(&Compiler.getASTContext()));
        return r;
    }

    /*Rewriter& getRewriter() {
        return TheRewriter;
        }*/
};

void printUsage() {
    std::cout << "\nUsage:\n\tqdtrans <single input file> [Clang options]\n\n";
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
    int result = Tool.run(newFrontendActionFactory<MyASTClassAction>().get());
    auto& myFiles = Tool.getFiles();
    
    DiagnosticOptions dopts;
    //TextDiagnosticPrinter *DiagClient = new clang::TextDiagnosticPrinter(llvm::errs(), &dopts, false);
    IntrusiveRefCntPtr<clang::DiagnosticIDs> DiagID(new clang::DiagnosticIDs());
    TextDiagnosticPrinter *DiagClient = new clang::TextDiagnosticPrinter(llvm::errs(), &dopts, false);
    DiagnosticsEngine Diags(DiagID, &dopts, DiagClient);
    SourceManager sm(Diags, myFiles, false);
    std::cout << "FILENAME: " << "\"" << filename << "\"" << std::endl;
    const FileEntry *myFileEntry = myFiles.getFile(filename);
    
    LangOptions lopts;
    Rewriter Rw = Rewriter(sm, lopts);
    //sm.overrideFileContents(myFileEntry, myFileBuffer.get().get(), false);
    std::vector<Replacement> mainrepv = (*RepMap)[filename];
    llvm::outs() << "[REPSSTART]\n";
    for(auto r : mainrepv) {
        std::cout << r.toString() << std::endl;
        r.apply(Rw);
        auto myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
        llvm::outs() << "[BUFSTART:" << myFileBuffer->size() << "]\n";
        
        myFileBuffer->write(llvm::outs());
        llvm::outs() << "[BUFEND]\n";
    }
    llvm::outs() << "[REPSEND]\n";
    /*auto myFileBuffer = myFiles.getBufferForFile(filename);
    if(!myFileBuffer) {
        std::cerr << "Nope" << std::endl;
        }*/
    /*auto myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
    llvm::outs() << "[BUFSTART]\n";
    myFileBuffer->write(llvm::outs());
    llvm::outs() << "[BUFEND]\n";*/
    myFiles.PrintStats();
    return result;
}
