import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp

/-! Scalar step for the cubic construction. Here `t = 1 / K` is reciprocal saturation. -/

noncomputable section
open Set Filter
open scoped Topology
namespace ERK.Scalar

/-- Cubic numerator of the reduced ERK drift, divided by the positive factor K². -/
def numerator (p q s t x : ℝ) : ℝ :=
  p * (1-x) * (t+x) * ((t+x) + s*(t+(1-x))) -
    q*x*s * (t+(1-x)) * (p*(t+x) + s*(t+(1-x)))

def denominator (p s t x : ℝ) : ℝ :=
  (t+(1-x)) * (t+x) * (p*(t+x) + s*(t+(1-x)))

/-- Reduced flux in the original positive saturation parameter K. -/
def flux (p q s K x : ℝ) : ℝ :=
  (K*(1-x)/(1+K*(1-x))) *
    (p*((1+K*x) + s*(1+K*(1-x))) / (p*(1+K*x) + s*(1+K*(1-x)))) -
    q*K*x*s/(1+K*x)

private theorem limit_identity (p q s x : ℝ) (h : 2*q*s = 1+p) :
    2 * numerator p q s 0 x = (1-p)*x*(1-x)*(p*x - s*(1-x)) := by
  unfold numerator
  linear_combination -x*(1-x)*(p*x+s*(1-x))*h

/-- The two interior sign tests use one positive reciprocal saturation. -/
theorem four_signs (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) :
    let s := (1+p)/(2*q)
    ∃ t l u : ℝ, 0 < t ∧ 0 < l ∧ l < u ∧ u < 1 ∧
      0 < numerator p q s t 0 ∧ numerator p q s t l < 0 ∧
      0 < numerator p q s t u ∧ numerator p q s t 1 < 0 := by
  dsimp only
  let s := (1+p)/(2*q)
  have hs : 0 < s := by dsimp [s]; positivity
  have hqs : 2*q*s = 1+p := by dsimp [s]; field_simp
  let l := s/(s+2*p)
  let u := 2*s/(2*s+p)
  have d₁ : 0 < s+2*p := by positivity
  have d₂ : 0 < 2*s+p := by positivity
  have hl : 0 < l := by exact div_pos hs d₁
  have hu : u < 1 := by exact (div_lt_iff₀ d₂).2 (by linarith)
  have hlu : l < u := by
    apply (div_lt_div_iff₀ d₁ d₂).2
    nlinarith [mul_pos hs hp]
  have hl1 : 0 < 1-l := by linarith
  have hu0 : 0 < u := hl.trans hlu
  have hu1 : 0 < 1-u := by linarith
  have el : p*l - s*(1-l) = -(s*p)/(s+2*p) := by
    dsimp [l]; field_simp; ring
  have eu : p*u - s*(1-u) = (s*p)/(2*s+p) := by
    dsimp [u]; field_simp; ring
  have hn : numerator p q s 0 l < 0 := by
    have h := limit_identity p q s l hqs
    rw [el] at h
    have hh := mul_neg_of_pos_of_neg (mul_pos (mul_pos (sub_pos.mpr hp') hl) hl1)
      (div_neg_of_neg_of_pos (neg_lt_zero.mpr (mul_pos hs hp)) d₁)
    linarith
  have hpv : 0 < numerator p q s 0 u := by
    have h := limit_identity p q s u hqs
    rw [eu] at h
    have hh := mul_pos (mul_pos (mul_pos (sub_pos.mpr hp') hu0) hu1) (div_pos (mul_pos hs hp) d₂)
    linarith
  have hc (x : ℝ) : Continuous (fun t => numerator p q s t x) := by unfold numerator; fun_prop
  have en : ∀ᶠ t in 𝓝[>] (0:ℝ), numerator p q s t l < 0 :=
    nhdsWithin_le_nhds ((hc l).continuousAt.eventually_lt continuousAt_const hn)
  have ep : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < numerator p q s t u :=
    nhdsWithin_le_nhds (continuousAt_const.eventually_lt (hc u).continuousAt hpv)
  have epos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hnt, hpt⟩ := (epos.and (en.and ep)).exists
  change 0 < t at ht
  refine ⟨t, l, u, ht, hl, hlu, hu, ?_, hnt, hpt, ?_⟩
  · simp only [numerator, sub_zero, add_zero, mul_zero, zero_mul, mul_one]
    positivity
  · simp only [numerator, sub_self, add_zero, zero_mul, mul_zero, mul_one, zero_sub]
    exact neg_lt_zero.mpr (by positivity)

private def cubic (a b c d x : ℝ) := a*x^3 + b*x^2 + c*x + d

/-- Cubic interpolation makes the degree bound a ring identity. -/
private theorem numerator_is_cubic (p q s t : ℝ) :
    ∃ a b c d, numerator p q s t = cubic a b c d := by
  let f := numerator p q s t
  let a := (f 2 - 3*f 1 + 3*f 0 - f (-1))/6
  let b := (f 1 + f (-1))/2 - f 0
  let c := (f 1 - f (-1))/2 - a
  exact ⟨a, b, c, f 0, by funext x; dsimp [a,b,c,f,numerator,cubic]; ring⟩

private theorem cubic_factor {a b c d i j k : ℝ} (hij : i < j) (hjk : j < k)
    (hi : cubic a b c d i = 0) (hj : cubic a b c d j = 0) (hk : cubic a b c d k = 0) :
    ∀ x : ℝ, cubic a b c d x = a * (x-i) * (x-j) * (x-k) := by
  let Q := fun x : ℝ => a*(x^2+x*i+i^2)+b*(x+i)+c
  have diff (x : ℝ) : cubic a b c d x - cubic a b c d i = (x-i)*Q x := by
    dsimp [Q,cubic]; ring
  have Qj : Q j = 0 := by
    apply (mul_eq_zero.mp _).resolve_left (sub_ne_zero.mpr hij.ne')
    rw [← diff, hj, hi]; ring
  have Qk : Q k = 0 := by
    apply (mul_eq_zero.mp _).resolve_left (sub_ne_zero.mpr (hij.trans hjk).ne')
    rw [← diff, hk, hi]; ring
  have hdiff : Q k - Q j = (k-j)*(a*(k+j+i)+b) := by dsimp [Q]; ring
  have hcoef : a*(k+j+i)+b = 0 := by
    apply (mul_eq_zero.mp _).resolve_left (sub_ne_zero.mpr hjk.ne')
    rw [← hdiff, Qk, Qj]; ring
  intro x
  have hQ (x : ℝ) : Q x = a*(x-j)*(x-k) := by
    dsimp [Q] at Qj ⊢
    linear_combination Qj + (x-j)*hcoef
  linear_combination diff x + hi + (x-i)*hQ x
private theorem numerator_sinks {p q s t l u : ℝ}
    (hl : 0 < l) (hlu : l < u) (hu : u < 1)
    (h0 : 0 < numerator p q s t 0) (hlv : numerator p q s t l < 0)
    (huv : 0 < numerator p q s t u) (h1 : numerator p q s t 1 < 0) :
    ∃ i k : ℝ, 0 < i ∧ i < k ∧ k < 1 ∧
      numerator p q s t i = 0 ∧ numerator p q s t k = 0 ∧
      deriv (numerator p q s t) i < 0 ∧ deriv (numerator p q s t) k < 0 := by
  let f := numerator p q s t
  have hc : Continuous f := by
    change Continuous (fun x => numerator p q s t x)
    unfold numerator
    fun_prop
  obtain ⟨i, hi, hfi⟩ := intermediate_value_Ioo' hl.le hc.continuousOn (show (0:ℝ) ∈ Ioo (f l) (f 0) from ⟨hlv,h0⟩)
  obtain ⟨j, hj, hfj⟩ := intermediate_value_Ioo hlu.le hc.continuousOn (show (0:ℝ) ∈ Ioo (f l) (f u) from ⟨hlv,huv⟩)
  obtain ⟨k, hk, hfk⟩ := intermediate_value_Ioo' hu.le hc.continuousOn (show (0:ℝ) ∈ Ioo (f 1) (f u) from ⟨h1,huv⟩)
  have hij := hi.2.trans hj.1
  have hjk := hj.2.trans hk.1
  have hik := hij.trans hjk
  obtain ⟨a,b,c,d,hcubic⟩ := numerator_is_cubic p q s t
  have hf : f = cubic a b c d := hcubic
  have fact := cubic_factor hij hjk (hf ▸ hfi) (hf ▸ hfj) (hf ▸ hfk)
  have eqf : f = fun x => a*(x-i)*(x-j)*(x-k) := by rw [hf]; exact funext fact
  have hneg : a < 0 := by
    change f 1 < 0 at h1
    rw [eqf] at h1
    by_contra! ha
    have hi1 := sub_pos.mpr (hik.trans hk.2)
    have hj1 := sub_pos.mpr (hjk.trans hk.2)
    have hk1 := sub_pos.mpr hk.2
    exact h1.not_ge (mul_nonneg (mul_nonneg (mul_nonneg ha hi1.le) hj1.le) hk1.le)
  have slope (x : ℝ) :
      deriv f x = a*(x-j)*(x-k) + a*(x-i)*(x-k) + a*(x-i)*(x-j) := by
    have dsub (z : ℝ) : HasDerivAt (fun y : ℝ => y-z) 1 x := (hasDerivAt_id' x).sub_const z
    rw [eqf]
    apply HasDerivAt.deriv
    apply ((((dsub i).const_mul a).fun_mul (dsub j)).fun_mul (dsub k)).congr_deriv
    ring
  refine ⟨i,k,hi.1,hik,hk.2,hfi,hfk,?_,?_⟩
  · change deriv f i < 0
    rw [slope]; simp only [sub_self,mul_zero,zero_mul,add_zero]
    exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hneg (sub_neg.mpr hij)) (sub_neg.mpr hik)
  · change deriv f k < 0
    rw [slope]; simp only [sub_self,mul_zero,zero_add]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (sub_pos.mpr hik)) (sub_pos.mpr hjk)

/-- Quotient representation of the physical scalar flux on the open substrate interval. -/
theorem flux_eq_quotient {p q s t x : ℝ} (hp : 0 < p) (hs : 0 < s) (ht : 0 < t)
    (hx : x ∈ Ioo (0:ℝ) 1) :
    flux p q s (1/t) x = numerator p q s t x / denominator p s t x := by
  have ha : 0 < 1-x := sub_pos.mpr hx.2
  have hb := hx.1
  have hA : 0 < t+(1-x) := by positivity
  have hB : 0 < t+x := by positivity
  have hC : 0 < p*(t+x)+s*(t+(1-x)) := by positivity
  have hU : 1+(1/t)*(1-x) = (t+(1-x))/t := by field_simp
  have hV : 1+(1/t)*x = (t+x)/t := by field_simp
  unfold flux numerator denominator
  rw [hU,hV]
  have hsum : p*((t+x)/t)+s*((t+(1-x))/t) = (p*(t+x)+s*(t+(1-x)))/t := by ring
  rw [hsum]
  field_simp [ht.ne',hA.ne',hB.ne',hC.ne']

private theorem lift_slope {p q s t x : ℝ} (hp : 0 < p) (hs : 0 < s) (ht : 0 < t)
    (hx : x ∈ Ioo (0:ℝ) 1) (hz : numerator p q s t x = 0)
    (hd : deriv (numerator p q s t) x < 0) :
    flux p q s (1/t) x = 0 ∧ deriv (flux p q s (1/t)) x < 0 := by
  have ha : 0 < 1-x := sub_pos.mpr hx.2
  have hb := hx.1
  have hden : 0 < denominator p s t x := by unfold denominator; positivity
  have eqnear : flux p q s (1/t) =ᶠ[𝓝 x] (fun y => numerator p q s t y / denominator p s t y) :=
    Filter.mem_of_superset (Ioo_mem_nhds hx.1 hx.2) (fun _ hy => flux_eq_quotient hp hs ht hy)
  have hnum : DifferentiableAt ℝ (numerator p q s t) x := by unfold numerator; fun_prop
  have hdif : DifferentiableAt ℝ (denominator p s t) x := by unfold denominator; fun_prop
  refine ⟨by rw [flux_eq_quotient hp hs ht hx,hz,zero_div],?_⟩
  rw [eqnear.deriv_eq,deriv_fun_div hnum hdif hden.ne', hz]
  simp only [zero_mul,sub_zero]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hd hden) (sq_pos_of_pos hden)

/-- At every prescribed processivity pair there is one finite positive K and two distinct
interior simple zeros of the physical reduced ERK flux, both with strictly negative slope. -/
theorem two_scalar_sinks (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) :
    let s := (1+p)/(2*q)
    ∃ K i k : ℝ, 0 < K ∧ 0 < i ∧ i < k ∧ k < 1 ∧
      flux p q s K i = 0 ∧ flux p q s K k = 0 ∧
      deriv (flux p q s K) i < 0 ∧ deriv (flux p q s K) k < 0 := by
  dsimp only
  let s := (1+p)/(2*q)
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨t,l,u,ht,hl,hlu,hu,h0,hlv,huv,h1⟩ := four_signs p q hp hp' hq
  obtain ⟨i,k,hi,hik,hk,zi,zk,di,dk⟩ := numerator_sinks hl hlu hu h0 hlv huv h1
  obtain ⟨ri,si⟩ := lift_slope hp hs ht ⟨hi,hik.trans hk⟩ zi di
  obtain ⟨rk,sk⟩ := lift_slope hp hs ht ⟨hi.trans hik,hk⟩ zk dk
  exact ⟨1/t,i,k,one_div_pos.mpr ht,hi,hik,hk,ri,rk,si,sk⟩

#print axioms two_scalar_sinks
/-- The flux is exactly the critical enzyme expression from the two fast balance equations. -/
theorem flux_eq_enzyme {p q s K x : ℝ} (hp : 0 < p) (hs : 0 < s) (hK : 0 < K)
    (hx : x ∈ Ioo (0:ℝ) 1) :
    let e := 1/(1+K*(1-x))
    let f := s/(1+K*x)
    flux p q s K x = K*(1-x)*e * (p*(e+f)/(p*e+f)) - q*K*x*f := by
  dsimp only
  let U := 1+K*(1-x)
  let V := 1+K*x
  have ha : 0 < 1-x := sub_pos.mpr hx.2
  have hb := hx.1
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hW : 0 < p*V+s*U := by positivity
  have hsum : 1/U+s/V = (V+s*U)/(U*V) := by field_simp
  have hpsum : p*(1/U)+s/V = (p*V+s*U)/(U*V) := by field_simp
  change (K*(1-x)/U)*(p*(V+s*U)/(p*V+s*U))-q*K*x*s/V =
    K*(1-x)*(1/U)*(p*(1/U+s/V)/(p*(1/U)+s/V))-q*K*x*(s/V)
  rw [hsum,hpsum]
  field_simp [hU.ne',hV.ne',hW.ne']

#print axioms flux_eq_enzyme
end ERK.Scalar
