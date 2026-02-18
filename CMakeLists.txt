cmake_minimum_required(VERSION 3.30)
project(MMP C)

set(CMAKE_C_STANDARD 99)

add_library(MMP SHARED bigint.c)
target_include_directories(MMP PUBLIC include)

add_executable(run_tests tests/test_main.c)

set(GMP_ROOT "C:/msys64/ucrt64")

find_path(GMP_INCLUDE_DIR
        NAMES gmp.h
        PATHS ${GMP_ROOT}/include
        NO_DEFAULT_PATH)

find_library(GMP_LIBRARY
        NAMES gmp
        PATHS ${GMP_ROOT}/lib
        NO_DEFAULT_PATH)

target_include_directories(run_tests PRIVATE ${GMP_INCLUDE_DIR})
target_link_libraries(run_tests PRIVATE MMP ${GMP_LIBRARY})
