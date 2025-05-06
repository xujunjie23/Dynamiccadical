#!/bin/bash
set -e

# 进入顶层目录
cd "$(dirname "$0")"

# 清理旧构建目录
rm -rf build
mkdir build
cd build

# 使用 configure 脚本配置编译环境
../configure

# 编译
make -j$(nproc)

# 复制可执行文件到顶层目录
cp cadical ../dynamiccadical
