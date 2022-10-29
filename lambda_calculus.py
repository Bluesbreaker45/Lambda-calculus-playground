zero = lambda f: lambda x: x
succ = lambda n: lambda f: lambda x: f(n(f)(x))
nums = []
n = zero
isZero = lambda n: n(lambda _: false)(true)
for i in range(0, 101):
  nums += [n]
  n = succ(n)

add = lambda m: lambda n: lambda f: lambda x: m(f)(n(f)(x))
mul = lambda m: lambda n: lambda f: m(n(f))
pow = lambda m: lambda n: n(m) # m ** n

#pred_pair = lambda n: n(lambda p: (p[1], p[1] + 1))((0, 0))
#pred = lambda n: pred_pair(n)[0]
# p = (a, b)
# WARNING: the order of pair reversed in the next 2 lines.
#         λn. n(λp:(    1 +  p[0]   , p[0]))   ((0, 0))          [1]
# PRED == λk.(k(λp.λu.u(SUCC(p TRUE))(p TRUE)) (λu.u ZERO ZERO) )FALSE

# so, a more understandable way to construct pred:

# 1. construct a pair producing pair (n - 1, n) for n
#    from that (pred, num): (0, 0) -> (0, 1) -> (1, 2) -> f(last_pair) -> ... n times.
#    then get the pair (n - 1, n)
# warning: pred_pair use cons as binary tuple, not a typical list!!!
pred_pair = lambda n: n(lambda p: cons(cdr(p))(succ(cdr(p))))(cons(zero)(zero))

# normal version
p_normal = lambda n: n(lambda p: cons(car(cdr(p)))(succ(car(cdr(p)))))(cons(zero)(cons(zero)(nil)))

# 2. get the second element of pair (n - 1, n)
pred = lambda n: car(pred_pair(n))

sub = lambda m: lambda n: n(pred)(m)

eq = lambda m: lambda n: andc(isZero(sub(m)(n)))(isZero(sub(n)(m)))

lt = lambda m: lambda n: andc(isZero(sub(m)(n)))(notc(isZero(sub(n)(m))))

toNum = lambda n: n(lambda x: x + 1)(0)

# if (cond)( exp1)(exp2)
# cond(exp1)(exp2)
# true(exp1)(exp2) = (lambda y: exp1)(exp2) = exp1
# false(exp1)(exp2) = (lambda y: y)(exp2) = exp2
# notc(true) = true(false)(true) = (lambda y: false)(true) =false
# notc(false) = false(false)(true) = (lambda y: y)(true) = true
# andc(false)(true) = false(true)(false) = false
# andc(true)(false) = true(false)(false) = false
# f(x1, x2 , ...,xn) -> f(x1)(x2).....(xn)
# lambda x1: lambda x2: ...,lambda xn: (function) <-> lambda (x1, x2, ..., xn): (function)

# Numeral section ends, bool section begins.

true = lambda x: lambda y: x
false = lambda x: lambda y: y
notc = lambda b: b(false)(true)
andc = lambda a: lambda b: a(b)(false)
orc = lambda a: lambda b: a(true)(b) # == lambda a: a(true)
ifc = lambda b: b

toBool = lambda b: b(True)(False)

# Bool section ends, pair section begins.
cons = lambda a: lambda b: lambda judge: judge(a)(b)
car = lambda pair: pair(true)
cdr = lambda pair: pair(false)
nil = lambda judge: judge(lambda _: _)(lambda _: _)(lambda z: z) # first 2 args are dummy
notNil = lambda pairOrNil: pairOrNil(lambda _: lambda __: lambda x: lambda y: x)
'''
Because in pure lambda calculus (without type), there is no way to distinguish a inner list or a non-list.
So you have to pass in the pattern of the list you passed in,like [non, [non, []], non].
If the length of the actual list is larger than the length of pattern list, the rest elements of the actual
list would be explained as the last element in the pattern list.
If the length of the actual list is less than the length of pattern list, the rest elements of the pattern
list would be ignored.
'''
# TODO
def printPairList(pair, pattern):
  def helper(prefix, pair, pattern):
    print("[")
    if (notNil(pair)):
      # TODO
      pass

  helper("", pair, pattern)

# corresponding nil below. mb this is more intuitive!
#nil = lambda judge: judge(lambda _: _)(lambda _: _)(lambda _: _)(true)
#isNil = lambda pairOrNil: pairOrNil(lambda _: lambda __: lambda x: lambda y: y)

"""
(It turns out that my nil is just one encoding result. There are other encodings
like nil = λx: true with isNil = λL.L(λh.λt.FALSE). And I am persuaded
(i.e. no proof) that pure λ-calculus is too weak to determine whether a term is
a num or a list without type system (just like that you cannot tell the type of
a string of bits in assembly language, and in church's encoding, zero equals to
false).
)
Inspiration:
first, think about it: which is possible (or easier) to construct, isNil or notNil?
I initially picked isNil, but hard to figure it out. Then I remembered that in
scheme a keyword is notNil. So, sneaky way!
(However, it turns out that both of them are possible, especially successfully
constructing notNil at first.)

Because in cons, a and b can be anything, so they(i.e. their value)
cannot be the clues for determining whether element is not a nil.

Like being the same type, true_pair and nil should both accept a judge_func.
(*degression: is this a constraint? does constraint useful in construction?)
So, try to consider times of application on judge.
In a true pair, the times of application on judge is 2,

so we try to construct a judge_func that return true if being applied chainly
for 2 times. And it could be jgNil = (lambda _: lambda __: lambda x: lambda y: x).

Then, we can make the nil apply other than 2 times on judge_func.
if 0 (impossible for creating a non-terminal) or 1 times, 
the value of a and b in cons *may* harm the result (since after
the application, the lambda term is ((lambda-term)(b)). b may matter). 
So consider 3 times. and first 2 args are dummy since jgNil (introduced in
paragraph 3) ignores the first 2 args. Then interestingly, 
(true(lambda x: x)) == false! So after the 2 application, the lambda-term is
true for sure. if we apply (lambda x: x) on it one more time, the value turns
false! That is what we want! 
(*Disgression: false(anything)(true) == true because false(anything) is 
lambda x: x, an identity function)

validation:
notNil(true_pair)
  -> cons(a)(b)(lambda _: lambda __: lambda x: lambda y: x)
  -> (lambda _: lambda __: lambda x: lambda y: x)(a)(b)
  -> lambda x: lambda y: x == true

notNil(nil)
  -> nil(lambda _: lambda __: lambda x: lambda y: x)
  -> (lambda _: lambda __: lambda x: lambda y: x)(lambda _: _)(lambda _: _)(lambda z: z)
  -> (lambda x: lambda y: x)(lambda z: z)
  -> lambda y: lambda z: z == false

*if you want to use isNil, choose the corresponding nil implementation.*

isNil(nil)
  -> nil(lambda _: lambda __: lambda x: lambda y: y)
  -> (lambda _: lambda __: lambda x: lambda y: y)
        (lambda _: _)(lambda _: _)(lambda _: _)(true)
  -> (lambda y: y)(true)
  -> true

isNil(true_pair)
  -> (lambda judge: judge(a)(b))(lambda _: lambda __: lambda x: lambda y: y)
  -> (lambda _: lambda __: lambda x: lambda y: y)(a)(b)
  -> (lambda x: lambda y: y) == false

"""

# Pair section ends, and recursion section begins.

fact = lambda x: 1 if x == 0 else x * fact(x - 1) # not allowed in lambda calculus.

Y = lambda f: (lambda x: f(x(x)))(lambda x: f(x(x))) # cause stack overflow in eager evaluation!!!

Z = (lambda f: (lambda x: f(lambda v: x(x)(v)))(lambda x: f(lambda v: x(x)(v)))) # computable in eager evaluation

fact_lambda = Z(lambda f: lambda n: 1 if n == 0 else n * f(n - 1))
'''
F(F(ZF))=F(ZF) = ZF
fact = Z(F)
fact(5) = Z(F)(5)
fact(5) = F(F(F(F(F(Y(F))))))(5)
Y(F) = (lambda x: F(x(x)))(lambda x: F(x(x)))
fact(5) = Y(F)(5)
= (lambda x: F(x(x)))(lambda x: F(x(x)))(5)

'''