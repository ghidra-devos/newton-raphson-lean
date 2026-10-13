newton's method in lean 4, with a full proof that it converges and how fast. no sorry anywhere, lean checks every step

the usual statement in textbooks is "if you start close enough to the root, newton converges quadratically". the problem is close enough. how close. this project writes the constants down and proves it for exactly that distance

what is proved

f is a real function with a root r. on the closed ball of radius rho around r assume

    |f'(x)| >= m > 0
    |f''(x)| <= M
    M * rho < 2 * m

then for every starting point x0 in that ball

    every iterate stays in the ball
    the iterates converge to r
    |x(n+1) - r| <= M / (2m) * |x(n) - r|^2
    C * |x(n) - r| <= (C * |x0 - r|) ^ (2^n)      with C = M / (2m)

the last line is the one that matters. once C * |x0 - r| is below 1/10, every step doubles the number of correct digits

the files

    NewtonRaphson/Basic.lean            the step, the sequence and the hypotheses
    NewtonRaphson/Taylor.lean           one step, |N(x) - r| <= M / (2m) * |x - r|^2
    NewtonRaphson/Convergence.lean      staying in the ball, convergence, the 2^n bound
    NewtonRaphson/Examples/Sqrt2.lean   x^2 - 2 from x0 = 3/2

the only real analysis is in Taylor.lean, a bound on the remainder of the tangent line. mathlib has taylor with the lagrange remainder but it wants iteratedDerivWithin and ContDiffOn, and the hypotheses here are plain HasDerivAt facts, so the proof goes through cauchy's mean value theorem with two functions picked for it. the comment above taylor_remainder_bound explains which ones and why

MATH.md walks through the same proof on paper, without lean

the sqrt 2 example

f(x) = x^2 - 2, x0 = 3/2, rho = 1/2, m = 1, M = 2. then C = 1 and the error simply squares every step. the file proves

    x1 = 17/12
    x2 = 577/408
    x3 = 665857/470832
    |x(n) - sqrt 2| <= (1/10) ^ (2^n)

so x3 is within 10^-8 of sqrt 2, proved and not just computed. it is actually much closer, about 1.6 * 10^-12. the starting bound of 1/10 comes from 1.4 <= sqrt 2 <= 1.5. with the lazier bound of 1/2 you only get 1/4, 1/16, 1/256, which is true but says nothing about how fast newton really is

building

you need elan, the lean version manager. the project pins lean 4.34.1 and the matching mathlib release, so

    lake exe cache get
    lake build

cache get downloads the compiled mathlib, a few GB. without it lake builds all of mathlib from source, which takes hours

what this is not

this is the local theorem, the root r is given. the real kantorovich theorem only looks at the starting point, f(x0), f'(x0) and a lipschitz constant for f', and proves that a root exists near x0 at all. that is the next thing i want to do here, along with newton in R^n with the jacobian

license

apache 2.0, see LICENSE
