# qdtrans-new
## How to compile

1. Follow Step 0 [here](https://clang.llvm.org/docs/LibASTMatchersTutorial.html).
2. Run the following: 
`cd ~/clang-llvm/llvm/tools/clang
mkdir tools/extra/loop-convert
echo 'add_subdirectory(loop-convert)' >> tools/extra/CMakeLists.txt
vim tools/extra/loop-convert/CMakeLists.txt`
3. Simply `cd ~/clang-llvm/build` and `ninja`.
