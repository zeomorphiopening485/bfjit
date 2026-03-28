cmake_minimum_required(VERSION 3.16)

project(bfjit LANGUAGES C)

set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_library(libbfjit STATIC
	include/bfjit.h
    include/bfjit_internal.h
    include/bflexer.h
    include/bfopt.h
    include/bfparser.h
	src/bfjit.c
    src/bfjit_backend.c
    src/bfjit_backend_shared.c
    src/bfjit_backend_x86_64.c
    src/bfjit_backend_aarch64.c
    src/bfjit_runtime.c
    src/bflexer.c
    src/bfopt.c
    src/bfparser.c
)

target_include_directories(libbfjit PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
set_target_properties(libbfjit PROPERTIES OUTPUT_NAME bfjit)

add_executable(bfjit src/main.c)
target_link_libraries(bfjit PRIVATE libbfjit)
