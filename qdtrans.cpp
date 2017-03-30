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

//#include "clang/Frontend/TextDiagnosticPrinter.h"

using namespace clang;
using namespace clang::tooling;

std::map<std::string, Replacements>* RepMap;

const char* argv1;

Replacement createAdjustedReplacementForCSR(CharSourceRange csr, ASTContext* TheContext, Replacements& reps, std::string text);

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
        (*RepMap)[TheContext->getSourceManager().getFileEntryForID(TheContext->getSourceManager().getMainFileID())->getName()] = Replacements(); //Initializing the Replacements object
    }

    bool VisitStmt(Stmt *s) {
        Stmt::child_iterator ChildIterator = s->child_begin();
        CharSourceRange CSRToAddTo;
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
                            CSRToAddTo = CharSourceRange::getCharRange((*ChildIterator)->getSourceRange());
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
                            inCrit = false;
                            PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                            PrintingPolicy& ppr = pp;
                            llvm::outs() << "NODE:\n";
                            (*ChildIterator)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                            os << ";\n"; //<< nodestring << "NL2\n";
                            std::cout << nodestring << std::endl;
                            CharSourceRange csr = CSRToAddTo;
                            SourceManager& sm = TheContext->getSourceManager();
                            StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                            Replacement rep = createAdjustedReplacementForCSR(csr, TheContext, (*RepMap)[filename.str()], nodetext.str());
                            Replacement& repr = rep;
                            std::cout << rep.toString() << std::endl; 
                            Replacements maprep = (*RepMap)[filename.str()];
                            Replacements reps = Replacements(repr);
                            maprep = maprep.merge(reps);
                            (*RepMap)[filename.str()] = maprep;
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
                    os << ";\n"; //<< nodestring << "NL2\n";
                    CharSourceRange csr = CharSourceRange::getCharRange((*ChildIterator)->getSourceRange());
                    SourceManager& sm = TheContext->getSourceManager();
                    StringRef filename = sm.getFileEntryForID(sm.getMainFileID())->getName();
                    Replacement rep = createAdjustedReplacementForCSR(csr, TheContext, (*RepMap)[filename.str()], nodetext.str());
                    Replacement& repr = rep;
                    std::cout << rep.toString() << std::endl; 
                    Replacements maprep = (*RepMap)[filename.str()];
                    Replacements reps = Replacements(repr);
                    maprep = maprep.merge(reps);
                    (*RepMap)[filename.str()] = maprep;
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
        std::cout << "hello world\n";
        auto r = std::unique_ptr<clang::ASTConsumer>(new MyASTConsumer(&Compiler.getASTContext()));
        std::cout << "hello world\n";
        return r;
    }

    /*Rewriter& getRewriter() {
        return TheRewriter;
        }*/
};

void printUsage() {
    std::cout << "\nUsage:\n\tqdtrans <single input file> [Clang options]\n\n";
}

Replacement createAdjustedReplacementForCSR(CharSourceRange csr, ASTContext* TheContext, Replacements& reps, std::string text) {
    SourceManager& sm = TheContext->getSourceManager();
    FullSourceLoc fslstart = FullSourceLoc(csr.getBegin(), sm);
    FullSourceLoc fslend = FullSourceLoc(csr.getEnd(), sm);
    unsigned start = std::get<1>(fslstart.getDecomposedLoc());
    unsigned length = 5;//std::get<1>(fslend.getDecomposedLoc())-start;
    Range range = Range(start, length);
    std::vector<Range> rangevecin(1);
    rangevecin[0] = range;   
    std::vector<Range> rangevecout = calculateRangesAfterReplacements(reps, rangevecin);
    Range adjrange = rangevecout[0];
    if(strcmp(argv1, sm.getFileEntryForID(sm.getMainFileID())->getName().str().c_str()) == 0) {
        std::cout << "Filenames match, replacements should be carrying over." << std::endl;
    } else {
        std::cout << "Filenames do not match, please fix." << std::endl;
    }
    std::cout << "\"" << sm.getFileEntryForID(sm.getMainFileID())->getName().str() << "\"" << std::endl;
    Replacement newReplacement = Replacement(sm.getFileEntryForID(sm.getMainFileID())->getName(), adjrange.getOffset(), adjrange.getLength(), StringRef(text));
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
    argv1 = argv[1];
    
    std::vector<std::string> args(argc-2);
    for(int i = 0; i < argc-2; i++) {
        args[i] = argv[i+2];
    }
    std::ifstream t(argv[1]);
    std::stringstream buffer;
    buffer << t.rdbuf();
    RepMap = &Tool.getReplacements();
    std::cout << RepMap << std::endl;
    int result = Tool.run(newFrontendActionFactory<MyASTClassAction>().get());
    auto& myFiles = Tool.getFiles();
    
    DiagnosticOptions dopts;
    //TextDiagnosticPrinter *DiagClient = new clang::TextDiagnosticPrinter(llvm::errs(), &dopts, false);
    IntrusiveRefCntPtr<clang::DiagnosticIDs> DiagID(new clang::DiagnosticIDs());
    DiagnosticsEngine Diags(DiagID, &dopts);
    SourceManager sm(Diags, myFiles, false);
    std::string filename = argv[1];//sm.getFileEntryForID(sm.getMainFileID())->tryGetRealPathName();
    std::cout << "FILENAME: " << "\"" << filename << "\"" << std::endl;
    const FileEntry *myFileEntry = myFiles.getFile(filename);
    
    LangOptions lopts;
    Rewriter Rw = Rewriter(sm, lopts);
    //sm.overrideFileContents(myFileEntry, myFileBuffer.get().get(), false);
    Replacements mainreps = (*RepMap)[filename];
    llvm::outs() << "[REPSSTART]\n";
    for(auto r : mainreps) {
        std::cout << r.toString() << std::endl;
    }
    llvm::outs() << "[REPSEND]\n";
    Tool.applyAllReplacements(Rw);
    /*auto myFileBuffer = myFiles.getBufferForFile(filename);
    if(!myFileBuffer) {
        std::cerr << "Nope" << std::endl;
        }*/
    auto myFileBuffer = Rw.getRewriteBufferFor(sm.getOrCreateFileID(myFileEntry, clang::SrcMgr::C_User));
    llvm::outs() << "[BUFSTART]\n";
    //std::cout << std::string((*myFileBuffer)->getBufferStart()) << std::endl;
    myFileBuffer->write(llvm::outs());
    llvm::outs() << "[BUFEND]\n";
    myFiles.PrintStats();
    return result;
}
