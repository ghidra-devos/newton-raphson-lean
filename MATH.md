the proof on paper, the same steps the lean files take, without lean

the step

we want f(x) = 0. at a guess x replace f by its tangent line, f(x) + f'(x)(t - x), and solve that for t instead

    N(x) = x - f(x) / f'(x)

newton is just x(n+1) = N(x(n))

the assumptions

r is a root, f(r) = 0. on the closed ball |x - r| <= rho

    |f'(x)| >= m > 0      the tangent is never close to flat
    |f''(x)| <= M         the function does not bend too much
    M * rho < 2 * m

the first two are what "f is nice near the root" means once you put numbers on it. the third ties them to the size of the ball, and everything below hangs on it

step 1, one step written exactly

    N(x) - r = x - r - f(x) / f'(x) = -(f(x) - f'(x)(x - r)) / f'(x)

just algebra. the thing on top is how far the tangent line at x misses the root, the remainder of a first order taylor expansion

step 2, the remainder

claim

    |f(x) - f'(x)(x - r)| <= M/2 * (x - r)^2

this is taylor with the lagrange remainder. the lean proof avoids mathlib's taylor theorem and does this instead. let

    phi(t) = f(t) + f'(t)(r - t)       the tangent at t, evaluated at r
    psi(t) = (t - r)^2

phi(r) = f(r) = 0 and phi(x) is exactly what we want to bound. differentiate phi, the two f' terms cancel

    phi'(t) = f'(t) + f''(t)(r - t) - f'(t) = f''(t)(r - t)

cauchy's mean value theorem on the interval between x and r gives a point c strictly in between with

    (psi(x) - psi(r)) * phi'(c) = (phi(x) - phi(r)) * psi'(c)
    (x - r)^2 * f''(c)(r - c) = phi(x) * 2(c - r)

c is not r, divide by c - r

    2 phi(x) = -(x - r)^2 f''(c)

c is between x and r so it is in the ball, |f''(c)| <= M, done

step 3, one step squares the error

put steps 1 and 2 together and use |f'(x)| >= m

    |N(x) - r| <= M / (2m) * |x - r|^2

call C = M / (2m)

step 4, staying in the ball

if |x - r| <= rho then

    |N(x) - r| <= C |x - r| * |x - r| <= C rho * |x - r|

and C rho = M rho / 2m < 1 is exactly the third assumption. so the next point is closer than this one and in particular still in the ball. by induction every iterate is, and

    |x(n) - r| <= (C rho)^n * |x0 - r|

which goes to zero. that is convergence

step 5, how fast

step 3 holds at every iterate now, since they all stay in the ball. multiply it by C

    C |x(n+1) - r| <= (C |x(n) - r|)^2

so e(n) = C |x(n) - r| squares every step, e(n) <= e(0)^(2^n). if e(0) = 1/10 then e(1) = 1/100, e(2) = 10^-4, e(3) = 10^-8. the number of correct digits doubles. step 4 alone would only give a fixed number of new digits per step, this is what makes newton fast

sqrt 2

f(x) = x^2 - 2, f'(x) = 2x, f''(x) = 2. take rho = 1/2. in the ball x >= sqrt 2 - 1/2 > 0.9, so |f'(x)| > 1.8 and m = 1 is fine. M = 2

    M rho = 1 < 2 = 2m

C = 2 / 2 = 1, so the error itself squares. from x0 = 3/2, which is within 1/10 of sqrt 2

    x1 = 17/12            error at most 1/100
    x2 = 577/408          error at most 1/10^4
    x3 = 665857/470832    error at most 1/10^8

the real errors are smaller, about 2.5 * 10^-3, 2.1 * 10^-6 and 1.6 * 10^-12, the bound only uses 1/10 for the first one

why "f'(r) is not zero" is not enough

f(x) = e^(1000x) - 1 has its root at 0 and f'(0) = 1000, far from zero. start at x = -0.1. there f'(x) = 1000 e^(-100), practically flat, and the step throws you to about e^100 / 1000, near 10^40. from there every step only moves back by about 1/1000. it does converge in the end, after something like 10^43 steps, so in practice it never does

nothing is wrong with newton here, the ball is the problem. on any ball around 0 that contains -0.1 the smallest |f'| is tiny and the largest |f''| is huge, and M rho < 2m fails badly. the theorem says nothing about such a start, and rightly so

how this relates to kantorovich

leonid kantorovich proved the real thing in 1948. he needs no root, only f(x0), f'(x0) and a lipschitz constant for f' near x0, and gets that a root exists, that newton converges to it and how fast. it also works in banach spaces, which is why it shows up all over numerical analysis. he later got the nobel prize in economics for linear programming, a different story

what is here is the simpler local version where the root is known. N is a contraction on the ball, which is the banach fixed point idea with the constants written out
