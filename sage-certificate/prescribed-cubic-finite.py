"""Check one full rational parameter choice from ERK-CUBIC by exact root counts."""
from sage.all import AA, QQ, NumberField, PolynomialRing, matrix

if not __debug__:
    raise SystemExit("Enable Python assertions for the certificate checks")
p, q = QQ(1)/2, QQ(2)/3
K, delta, eta = QQ(1024), QQ(1)/10**6, QQ(1)/10**6
kinase_total = eta
phosphatase_total = eta * (1+p)/(2*q)


def balances(point):
    """Original physical-time balances in the order of the primary paper, equation (4)."""
    a, e, f, u_f, v_f, w_f, v_e, w_e, c, d, u_e, b = point
    return (
        -K*a*e + q*v_f/delta + w_f/delta,
        -K*a*e - (c+d)*e/delta + (v_e+w_e)/delta,
        -K*b*f - c*f/delta + (v_f+w_f)/delta,
        K*b*f-u_f, u_f-v_f/delta, (c*f-w_f)/delta,
        u_e+(c*e-v_e)/delta, (d*e-w_e)/delta,
        ((1-p)*v_e-(e+f)*c)/delta,
        ((1-q)*v_f-d*e)/delta,
        K*a*e-u_e, -K*b*f+(p*v_e+w_e)/delta,
    )


def totals(x):
    return (x[0] + sum(x[3:]), x[1] + x[6] + x[7] + x[10], sum(x[2:6]))


# Eliminate using the concentration z of free S01 rather than an enzyme or saturation limit.
P = PolynomialRing(QQ, "z")
z = P.fraction_field().gen()
alpha = 1/(1-p)
beta = p*alpha/q
Ae = alpha + (1-q)*beta + alpha*p/delta
Af = alpha + (1-q)*beta + alpha/delta
Be = beta*(1+1/delta)
Bf = Be + 1
den = (1+Ae*z)*(1+Bf*z) - Af*Be*z*z
e_num = kinase_total*(1+Bf*z) - Af*z*phosphatase_total
f_num = (1+Ae*z)*phosphatase_total - Be*z*kinase_total
assert e_num.numerator().gcd(den.numerator()) == 1
e, f = e_num/den, f_num/den
v_e = alpha*(e+f)*z
u_e = alpha*(p*e+f)*z/delta
v_f = p*v_e/q
u_f = v_f/delta
w_e = (1-q)*v_f
state = (u_e/(K*e), e, f, u_f, v_f, f*z, v_e, w_e, z, w_e/e, u_e, u_f/(K*f))
assert all(value == 0 for value in balances(state))
s, et, ft = totals(state)
assert et == kinase_total and ft == phosphatase_total
residual = s-1
elim = P(residual.numerator()).monic()

ring = PolynomialRing(QQ, names=tuple("x"+str(i) for i in range(1, 13)))
variables = ring.gens()
jac = [[eq.derivative(var) for var in variables] for eq in balances(variables)]
counts = []
for factor, mult in elim.factor():
    for z_root, _ in factor.roots(AA):
        if z_root <= 0 or any(value.denominator()(z_root) == 0 for value in state):
            continue
        field = QQ if factor.degree() == 1 else NumberField(factor, "w", embedding=z_root)
        coordinate = -factor[0]/factor[1] if field is QQ else field.gen()
        at = [value.numerator()(coordinate)/value.denominator()(coordinate) for value in state]
        if not all(AA(value) > 0 for value in at):
            continue
        assert mult == 1 and totals(at) == (1, kinase_total, phosphatase_total)
        # Work in physical coordinates. Three zero eigenvalues arise from the totals.
        charpoly = matrix(field, [[entry(*at) for entry in row] for row in jac]).charpoly()
        assert charpoly.valuation() == 3
        coeff = list(reversed(charpoly.list()[3:]))
        h = matrix(field, 9, 9, lambda i, j: coeff[2*j-i+1] if 0 <= 2*j-i+1 <= 9 else 0)
        prev = field.one()
        signs = [1]
        for k in range(1, 10):
            det = h[:k, :k].det()
            assert det
            signs.append(AA(det/prev).sign())
            prev = det
        count = sum(a != b for a, b in zip(signs, signs[1:]))
        print(f"x9={z_root}; right-half-plane eigenvalues={count}")
        counts.append(count)
assert sorted(counts) == [0, 0, 1]
print("Checked exact class totals, distinct positive equilibria, and physical-time spectra.")
