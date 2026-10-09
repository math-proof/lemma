#pragma once
#include "../utility.h"

VectorI& _run_mst_decoding(Matrix &scores, VectorI &head_indices);

VectorI& decode_mst(Matrix &scores, VectorI &heads, bool projective=true);

bool is_projective(const VectorI &head_indices);

void nonprojective_adjustment(VectorI &head_indices);

//https://github.com/XuezheMax/NeuroNLP2
//Stack-Pointer Networks for Dependency Parsing.pdf
//https://blog.csdn.net/appleml/article/details/80967336?utm_medium=distribute.pc_relevant.none-task-blog-BlogCommendFromMachineLearnPai2-3.control&depth_1-utm_source=distribute.pc_relevant.none-task-blog-BlogCommendFromMachineLearnPai2-3.control
