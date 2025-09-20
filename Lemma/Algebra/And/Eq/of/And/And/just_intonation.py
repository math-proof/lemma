from util import *


@apply
def apply(et_eq_8, et_eq_5):
    from Lemma.Algebra.And.Eq.of.And.just_intonation import equate
    (r_33, S[S.One / 2]), (r_77, r_11), (S[r_11], r_11_sharp), (r_22, r_22_sharp), (S[r_11_sharp], S[r_22]), (S[r_22_sharp], S[r_33]) = \
    et_eq_8.of(And[Equal[6]])

    λ_7, λ_7_low = r_77.of(Expr / Expr)
    λ_1_dot, λ_1 = r_11.of(Expr / Expr)
    λ_2_dot, λ_2 = r_22.of(Expr / Expr)
    λ_3_dot, λ_3 = r_33.of(Expr / Expr)
    λ_1_dot_sharp, λ_1_sharp = r_11_sharp.of(Expr / Expr)
    λ_2_dot_sharp, λ_2_sharp = r_22_sharp.of(Expr / Expr)

    (r_36, S[Number(2) / 3]), (r_51, r_51_sharp), (r_62, r_62_sharp), (r_73, r_14), (S[r_14], r_14_sharp), (r_25, r_25_sharp), (r_47_low, S[r_51]), (S[r_51_sharp], S[r_62]), (S[r_62_sharp], S[r_73]), (S[r_14_sharp], S[r_25]), (S[r_25_sharp], S[r_36]) = \
    et_eq_5.of(And[Equal[11]])

    λ_4_sharp, S[λ_7_low] = r_47_low.of(Expr / Expr)
    λ_5, S[λ_1] = r_51.of(Expr / Expr)
    λ_5_sharp, S[λ_1_sharp] = r_51_sharp.of(Expr / Expr)
    λ_6, S[λ_2] = r_62.of(Expr / Expr)
    λ_6_sharp, S[λ_2_sharp] = r_62_sharp.of(Expr / Expr)
    S[λ_7], S[λ_3] = r_73.of(Expr / Expr)

    S[λ_1_dot], λ_4 = r_14.of(Expr / Expr)
    S[λ_1_dot_sharp], S[λ_4_sharp] = r_14_sharp.of(Expr / Expr)

    S[λ_2_dot], S[λ_5] = r_25.of(Expr / Expr)
    S[λ_2_dot_sharp], S[λ_5_sharp] = r_25_sharp.of(Expr / Expr)
    S[λ_3_dot], S[λ_6] = r_36.of(Expr / Expr)

    return equate(λ_1_sharp / λ_1, λ_2_sharp / λ_2, λ_4_sharp / λ_4, λ_5_sharp / λ_5, λ_6_sharp / λ_6, Number(2) ** 11 / 3 ** 7), \
        equate(λ_1 / λ_7_low, λ_2 / λ_1_sharp, λ_3 / λ_2_sharp, λ_4 / λ_3, λ_5 / λ_4_sharp, λ_6 / λ_5_sharp, λ_7 / λ_6_sharp, Number(3) ** 5 / 2 ** 8), \
        Equal(λ_2 / λ_1, Number(8) / 9), Equal(λ_4 / λ_1, Number(3) / 4)


@prove
def prove(Eq):
    from Lemma import Algebra
    from Lemma.Algebra.And.Eq.of.And.just_intonation import equate
    λ_7_low = Symbol(r"λ_{\underset{\mathbf{\Large{.}}}{7}}", real=True)
    λ_1, λ_2, λ_3, λ_4, λ_5, λ_6, λ_7 = Symbol(real=True)
    λ_1_sharp = Symbol(r"λ_{{^\#}1}", real=True)
    λ_2_sharp = Symbol(r"λ_{{^\#}2}", real=True)
    λ_4_sharp = Symbol(r"λ_{{^\#}4}", real=True)
    λ_5_sharp = Symbol(r"λ_{{^\#}5}", real=True)
    λ_6_sharp = Symbol(r"λ_{{^\#}6}", real=True)
    λ_1_dot = Symbol(r"λ_{\overset{\mathbf{\Large{.}}}{1}}", real=True)
    λ_1_dot_sharp = Symbol(r"λ_{{^\#}{\overset{\mathbf{\Large{.}}}{1}}}", real=True)
    λ_2_dot = Symbol(r"λ_{\overset{\mathbf{\Large{.}}}{2}}", real=True)
    λ_2_dot_sharp = Symbol(r"λ_{{^\#}{\overset{\mathbf{\Large{.}}}{2}}}", real=True)
    λ_3_dot = Symbol(r"λ_{\overset{\mathbf{\Large{.}}}{3}}", real=True)
    (Eq.et_h, Eq.et_c), (Eq.et_d5, Eq.et_d7, Eq.D_2, Eq.q_4) = apply(equate(λ_7 / λ_7_low, λ_1_dot / λ_1, λ_1_dot_sharp / λ_1_sharp, λ_2_dot / λ_2, λ_2_dot_sharp / λ_2_sharp, λ_3_dot / λ_3, S.One / 2),
                equate(λ_4_sharp / λ_7_low, λ_5 / λ_1, λ_5_sharp / λ_1_sharp, λ_6 / λ_2, λ_6_sharp / λ_2_sharp, λ_7 / λ_3, λ_1_dot / λ_4,  λ_1_dot_sharp / λ_4_sharp,  λ_2_dot / λ_5,  λ_2_dot_sharp / λ_5_sharp,  λ_3_dot / λ_6,  Number(2) / 3))

    # two degree of musical tones: d_*, deux
    Eq.d_1_sharp, Eq.d_2_sharp, Eq.d_4_sharp, Eq.d_5_sharp, Eq.d_6_sharp = Algebra.And.given.And.Eq.continued.apply(Eq.et_d5, Number(2) ** 11 / 3 ** 7)

    Eq.d_1, Eq.d_2, Eq.d_3, Eq.d_4, Eq.d_5, Eq.d_6, Eq.d_7 = Algebra.And.given.And.Eq.continued.apply(Eq.et_d7, Number(3) ** 5 / 2 ** 8)

    # eight degree of musical tones: h_*, huit
    Eq.h_7, Eq.h_1, Eq.h_1_sharp, Eq.h_2, Eq.h_2_sharp, Eq.h_3 = Algebra.And.Eq.of.And.just_intonation.apply(Eq.et_h, S.One / 2)

    Eq << Eq.et_c.subs(Eq.h_7.reversed * λ_7_low * 2, Eq.h_1 * λ_1, Eq.h_1_sharp * λ_1_sharp, Eq.h_2 * λ_2, Eq.h_2_sharp * λ_2_sharp, Eq.h_3 * λ_3)

    # five degree of musical tones: c_*, cinq
    Eq.c_4_sharp, Eq.c_5, Eq.c_5_sharp, Eq.c_6, Eq.c_6_sharp, Eq.c_7, Eq.c_1, Eq.c_1_sharp, Eq.c_2, Eq.c_2_sharp, Eq.c_3 = Algebra.And.Eq.of.And.just_intonation.apply(Eq[-1], Number(2) / 3)

    Eq << Eq.c_5 * Eq.c_2 * 2

    Eq << 1 / (Eq.c_1 * 2)

    Eq.c_4_sharp, Eq.D_4_sharp, Eq.D_3, Eq.D_2_sharp = Eq.h_7 * Eq.c_4_sharp * 2, Eq.c_4_sharp * Eq.c_7 * 2, Eq.c_6 * Eq.c_3 * 2, Eq.c_5_sharp * Eq.c_2_sharp * 2

    Eq.q_3 = Eq.c_4_sharp / Eq.D_4_sharp

    Eq.q_4_sharp = 1 / Eq.c_1_sharp / 2

    Eq.t_3 = Eq.q_4_sharp / Eq.D_4_sharp

    Eq << Eq.t_3 / Eq.D_3

    Eq << Eq.D_2 / Eq.d_2

    Eq << Eq.D_2_sharp / Eq.d_2

    Eq << Eq.D_3 / Eq.d_2_sharp

    Eq.T_3 = Eq.d_1_sharp * Eq.t_3

    Eq << Eq.q_4 / Eq.T_3

    Eq << Eq.D_4_sharp / Eq.d_4

    Eq.Q_4_sharp = Eq.T_3 * Eq.d_4 * Eq.d_4_sharp

    Eq << Eq.c_5 / Eq.Q_4_sharp

    Eq << Eq.c_5_sharp * Eq.d_1_sharp / Eq.c_5

    Eq.t_5_sharp = Eq.d_4_sharp * Eq.d_5 * Eq.d_5_sharp

    Eq.Q_5_sharp = Eq.D_3 * Eq.d_4 * Eq.t_5_sharp

    Eq << Eq.c_6 / Eq.Q_5_sharp

    Eq << Eq.d_4 * Eq.t_5_sharp * Eq.d_3

    Eq << Eq.c_6_sharp / Eq[-1] / Eq.d_6

    Eq << Eq.t_5_sharp * Eq.d_4 * Eq.d_6 * Eq.d_6_sharp

    Eq << Eq.c_7 / Eq[-1]

    Eq << Eq.q_3 / Eq.T_3

    # 针对纯律，我的基本假设是：
    # 一，纯八度之间的波长之比为1/2, 即等式Eq[0]成立;
    # 二，根据三分损宜法，五度相生律，纯5度之间的波长之比为2/3，即等式Eq[1]成立(除了高音4/升6之外);
    # 根据以上两点，通过消元法解方程后（18个变量，17个方程），可以推导：
    # 一，5个升降音与还原音之间的波长比相等，也即一个升降音与还原音之间的波长比为2048/2187, 即等式组Eq[2]成立，等价说法：钢琴上黑键音与相邻上一个白键音的频率比相等;
    # 二，7个还原音与之前一个半音之间的波长比相等，也即一个小二度使波长/弦长变为原来的243/256，即等式组Eq[3]成立，等价说法：钢琴上一个白键音与相邻上一个音阶（白键或黑键）的频率比相等;
    # 三，一个大二度使波长/弦长变为原来的8/9；
    # 四，一个纯四度使波长/弦长变为原来的3/4；
    # 百科参考资料：https://baike.baidu.com/pic/%E7%BA%AF%E5%BE%8B/659996/0/834344afb490879efaed5021?fr=lemma&ct=single# aid=0&pic=834344afb490879efaed5021




if __name__ == '__main__':
    run()
# created on 2018-11-24
# updated on 2021-11-25