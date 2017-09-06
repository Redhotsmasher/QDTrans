# qdtrans-new
## How to compile

1. Follow Step 0 [here](https://clang.llvm.org/docs/LibASTMatchersTutorial.html).
2. Clone this repo and copy the resulting folder `QDTrans` into `~/clang-llvm/llvm/tools/clang`.
3. Run the following:
```
cd ~/clang-llvm/llvm/tools/clang
echo 'add_subdirectory(QDTrans)' >> tools/extra/CMakeLists.txt
```
4. Simply `cd ~/clang-llvm/build` and `ninja`.
