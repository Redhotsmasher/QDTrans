set(LLVM_LINK_COMPONENTS support)

add_clang_executable(qdtrans
  qdtrans.cpp
  )
add_clang_executable(qdtrans
  dumptree.cpp
  )
target_link_libraries(qdtrans
  clangTooling
  clangBasic
  clangASTMatchers
  )

