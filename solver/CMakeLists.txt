cmake_minimum_required(VERSION 3.16)
project(shell_turbulence LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

find_package(Threads REQUIRED)

# Contraction into fused multiply-adds and -ffast-math would change rounding
# and are deliberately excluded.
set(SABRA_FLAGS -O3 -ffp-contract=off -fno-fast-math)
string(REPLACE ";" " " SABRA_FLAGS_TEXT "${SABRA_FLAGS}")

add_library(sabra SHARED src/sabra_capi.cpp)
target_include_directories(sabra PUBLIC include)
target_compile_options(sabra PRIVATE ${SABRA_FLAGS})
target_compile_definitions(sabra PRIVATE SABRA_BUILD_FLAGS="cmake ${SABRA_FLAGS_TEXT}")
target_link_libraries(sabra PRIVATE Threads::Threads)

add_executable(sabra_tests tests/test_sabra.cpp)
target_include_directories(sabra_tests PRIVATE include)
target_compile_options(sabra_tests PRIVATE ${SABRA_FLAGS})
target_link_libraries(sabra_tests PRIVATE Threads::Threads)

add_executable(sabra_bench bench/bench_sabra.cpp)
target_include_directories(sabra_bench PRIVATE include)
target_compile_options(sabra_bench PRIVATE ${SABRA_FLAGS})
target_link_libraries(sabra_bench PRIVATE Threads::Threads)

enable_testing()
add_test(NAME sabra_tests COMMAND sabra_tests)
