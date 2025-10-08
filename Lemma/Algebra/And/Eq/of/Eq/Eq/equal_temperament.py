from util import *



@apply
def apply(eq_1_high, et_eq):
    λ_1_high, λ_1 = eq_1_high.of(Equal[Expr / Expr, S.One / 2])

    (r_12, r_22), (r_23, r_34), (S[r_34], r_44), (r_45, r_55), (r_56, r_66), (r_67, r_71), (r_11, S[r_12]), (S[r_22], S[r_23]), (S[r_44], S[r_45]), (S[r_55], S[r_56]), (S[r_66], S[r_67]) = et_eq.of(And[Equal[11]])

    λ_1_sharp, S[λ_1] = r_11.of(Expr / Expr)
    λ_2, S[λ_1_sharp] = r_12.of(Expr / Expr)

    λ_2_sharp, S[λ_2] = r_22.of(Expr / Expr)

    λ_3, S[λ_2_sharp] = r_23.of(Expr / Expr)

    λ_4, S[λ_3] = r_34.of(Expr / Expr)

    λ_4_sharp, S[λ_4] = r_44.of(Expr / Expr)

    λ_5, S[λ_4_sharp] = r_45.of(Expr / Expr)

    λ_5_sharp, S[λ_5] = r_55.of(Expr / Expr)

    λ_6, S[λ_5_sharp] = r_56.of(Expr / Expr)

    λ_6_sharp, S[λ_6] = r_66.of(Expr / Expr)

    λ_7, S[λ_6_sharp] = r_67.of(Expr / Expr)

    S[λ_1_high], S[λ_7] = r_71.of(Expr / Expr)

    w = (S.One / 2) ** (S.One / 12)

    return Equal(λ_1_sharp / λ_1, w), Equal(λ_4 / λ_3, w), Equal(λ_2 / λ_1, w ** 2), Equal(λ_4 / λ_1, w ** 5)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    from Lemma.Algebra.And.Eq.of.And.just_intonation import equate

    λ_1, λ_2, λ_3, λ_4, λ_5, λ_6, λ_7 = Symbol(real=True, positive=True)
    λ_1_sharp = Symbol(r"λ_{1^\#}", real=True, positive=True)
    λ_2_sharp = Symbol(r"λ_{2^\#}", real=True, positive=True)
    λ_4_sharp = Symbol(r"λ_{4^\#}", real=True, positive=True)
    λ_5_sharp = Symbol(r"λ_{5^\#}", real=True, positive=True)
    λ_6_sharp = Symbol(r"λ_{6^\#}", real=True, positive=True)
    λ_1_high = Symbol(r"λ_\dot{1}", real=True, positive=True)
    Eq << apply(Equal(λ_1_high / λ_1, S.One / 2),
                equate(λ_1_sharp / λ_1, λ_2 / λ_1_sharp, λ_2_sharp / λ_2, λ_3 / λ_2_sharp, λ_4 / λ_3, λ_4_sharp / λ_4, λ_5 / λ_4_sharp, λ_5_sharp / λ_5, λ_6 / λ_5_sharp, λ_6_sharp / λ_6, λ_7 / λ_6_sharp, λ_1_high / λ_7))

    w = Symbol(λ_1_sharp / λ_1)
    Eq.r_1_sharp = w.this.definition.reversed

    Eq << Bool.And_And.of.And.apply(Eq[1], None)

    Eq.r_2 = Eq[12].subs(Eq.r_1_sharp).reversed

    Eq.r_2_sharp = Eq[6].subs(Eq.r_2).reversed

    Eq.r_3 = Eq[13].subs(Eq.r_2_sharp).reversed

    Eq.r_4 = Eq[7].subs(Eq.r_3).reversed

    Eq.r_4_sharp = Eq[8].subs(Eq.r_4).reversed

    Eq.r_5 = Eq[14].subs(Eq.r_4_sharp).reversed

    Eq.r_5_sharp = Eq[9].subs(Eq.r_5).reversed

    Eq.r_6 = Eq[15].subs(Eq.r_5_sharp).reversed

    Eq.r_6_sharp = Eq[10].subs(Eq.r_6).reversed

    Eq.r_7 = Eq[16].subs(Eq.r_6_sharp).reversed

    Eq.r_1_high = Eq[11].subs(Eq.r_7).reversed

    Eq << Eq.r_1_sharp * Eq.r_2_sharp * Eq.r_4_sharp * Eq.r_5_sharp * Eq.r_6_sharp * Eq.r_2 * Eq.r_3 * Eq.r_4 * Eq.r_5 * Eq.r_6 * Eq.r_7 * Eq.r_1_high

    Eq << Eq[-1].subs(Eq[0]).reversed

    Eq << Eq[-1] ** (S.One / 12)

    Eq << Eq.r_1_sharp.subs(Eq[-1])

    Eq << Eq.r_4.subs(Eq[-1])

    Eq << (Eq.r_1_sharp * Eq.r_2).subs(Eq[-1])

    Eq << (Eq.r_1_sharp * Eq.r_2 * Eq.r_2_sharp * Eq.r_3 * Eq.r_4).subs(Eq[-1])

    # 十二平均律的基本假设是：
    # 一，纯八度之间的波长之比为1/2, 即等式Eq[0]成立;
    # 二，5个升降音与还原音之间的波长比相等，7个还原音与之前一个半音之间的波长比相等，且这两个比例相同，即等式组Eq[1]成立;
    # 根据以上两点可以推导：
    # 一，一个升降音与还原间波长比为2**(11/12)/2=0.9438743126816935,
    # 比较与纯律得出的值   2048/2187=0.9364426154549611，基本相同;
    # 二，一个小二度使波长变为原来的2**(11/12)/2=0.9438743126816935，
    # 比较与纯律得出的值     243/256=0.94921875，也基本相同；
    # 三，一个大二度使波长变为原来的2**(5/6)/2=0.8908987181403393,
    # 比较与纯律得出的值       8/9=0.8888888888888888, 基本相同；
    # 四，一个纯四度使波长变为原来的2**(7/12)/2=0.7491535384383408，
    # 比较与纯律得出的值        3/4=0.75，基本相同；
    # 如果想得出各音阶频率之比，可以从波长之比的倒数得出，且对于弦乐器，弦长之比等于波长之比。
    # 参考资料：律学新说，https://baike.baidu.com/item/%E5%BE%8B%E5%AD%A6%E6%96%B0%E8%AF%B4/5626236?fr=aladdin


if __name__ == '__main__':
    run()
# created on 2018-10-10
# updated on 2021-11-23
