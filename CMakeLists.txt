set(LLVM_LINK_COMPONENTS support)

add_clang_executable(qdtrans
  qdtrans.cpp
  )
target_link_libraries(qdtrans
  clangTooling
  clangBasic
  clangASTMatchers
  )

