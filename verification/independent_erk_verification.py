"""Exact finite falsification test of the cubic construction, from paper equations (4)-(5)."""
from sage.all import AA, QQ, NumberField, PolynomialRing, matrix


def steady_state_curve(ring, p, q, K, delta, eta):
    """Return the physical state on both enzyme totals, as a function of free E/F."""
    ratio = ring.fraction_field().gen()
    s = (1 + p) / (2 * q)
    h = p * (1 + ratio) / (1 + p * ratio)
    b = ratio * h / q
    c = delta * (1 - p) * K * ratio / (1 + p * ratio)
    d = delta * (1 - q) * K * b / ratio
    kinase = (1 + delta) * K + c + d
    phosphatase = (1 + delta) * K * b + c
    divisor = phosphatase - s * ratio * kinase
    if divisor(1 / s) == 0:
        raise ValueError("The exceptional ratio E/F=1/s needs separate analysis")
    A = (s * ratio - 1) / divisor
    B, C, D = A*b, A*c, A*d
    E = eta / (1 + A*kinase)
    F = s*eta / (1 + A*phosphatase)
    state = (A, E, F, K*B*F, delta*K*B*F, C*F, delta*K*A*E+C*E,
             D*E, C, D, K*A*E, B)
    if E != ratio*F or E + state[6]+state[7]+state[10] != eta or sum(state[2:6]) != s*eta:
        raise ArithmeticError("Enzyme identities failed")
    return state


def derivatives(x, p, q, K, delta):
    """Physical-time equations in the species order of the original article."""
    a, e, f, u, v, w, i, j, c, d, h, b = x
    return (-K*a*e + (q*v+w)/delta,
            -K*a*e + (i+j-(c+d)*e)/delta,
            -K*b*f + (v+w-c*f)/delta,
            K*b*f-u, u-v/delta, (c*f-w)/delta,
            h+(c*e-i)/delta, (d*e-j)/delta,
            ((1-p)*i-(e+f)*c)/delta, ((1-q)*v-e*d)/delta,
            K*a*e-h, -K*b*f+(p*i+j)/delta)


def verify(p, q, K, delta, eta, expected):
    ring = PolynomialRing(QQ, "ratio")
    state = steady_state_curve(ring, p, q, K, delta, eta)
    if any(derivatives(state, p, q, K, delta)):
        raise ArithmeticError("A published equation has a nonzero residual")
    substrate = state[0] + sum(state[3:])
    polynomial = ring((substrate-1).numerator())
    coords = PolynomialRing(QQ, names=["x"+str(i) for i in range(4, 13)]).gens()
    u, v, w, i, j, c, d, h, b = coords
    physical = (1-sum(coords), eta-i-j-h, eta*(1+p)/(2*q)-u-v-w, *coords)
    restricted = derivatives(physical, p, q, K, delta)[3:]
    jac = [[eq.derivative(z) for z in coords] for eq in restricted]
    observed = []
    for factor, multiplicity in polynomial.factor():
        for root, _ in factor.roots(AA):
            if root <= 0 or any(entry.denominator()(root) == 0 for entry in state):
                continue
            field = QQ if factor.degree() == 1 else NumberField(factor, "a", embedding=root)
            at_root = -factor[0]/factor[1] if field is QQ else field.gen()
            x = [v.numerator()(at_root)/v.denominator()(at_root) for v in state]
            if any(AA(v) <= 0 for v in x):
                continue
            if multiplicity != 1 or x[0]+sum(x[3:]) != 1:
                raise ArithmeticError("Nonsimple root or inconsistent substrate total")
            tangent = matrix(field, [[entry(*x[3:]) for entry in row] for row in jac])
            coeff = tangent.charpoly().list()[::-1]
            hurwitz = matrix(field, 9, 9, lambda i, j: coeff[2*j-i+1] if 0 <= 2*j-i+1 <= 9 else 0)
            prev = field.one()
            signs = [1]
            for k in range(1, 10):
                det = hurwitz[:k, :k].det()
                if not det:
                    raise ArithmeticError("Zero Hurwitz minor")
                signs.append(AA(det/prev).sign())
                prev = det
            unstable = sum(a != b for a,b in zip(signs, signs[1:]))
            observed.append((AA(x[-1]), unstable))
    observed.sort()
    if [count for _,count in observed] != expected:
        raise ArithmeticError(f"Expected {expected}, obtained {observed}")
    print(f"p={p}, q={q}, K={K}, delta={delta}, eta={eta}")
    for B, count in observed:
        print(f"  free S11={B.numerical_approx(digits=8)}; right-half-plane directions={count}")


if __name__ == "__main__":
    p, q = QQ(999)/1000, QQ(9999)/10000
    small = QQ(1)/10**12
    verify(p, q, 1, small, small, [0])
    verify(p, q, 2**20, small, small, [0,1,0])
