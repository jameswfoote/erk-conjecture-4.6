import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The minimally bistable ERK model, equations (4) and (5) of Conradi,
Obatake, Shiu and Tang. All vector indices are zero-based. -/
noncomputable section

namespace ERK.Model

abbrev State := Fin 12 → ℝ
abbrev Rates := Fin 13 → ℝ
abbrev Chart := Fin 9 → ℝ
abbrev Totals := Fin 3 → ℝ

/-- Rates in the order k1,k3,kcat,kon,koff,l1,l3,lcat,loff,m2,m3,n1,n3.
Species in the order S00,E,F,S11F,S10F,S01F,S01E,S10E,S01,S10,S00E,S11. -/
def flux (k : Rates) (x : State) : Rates :=
  ![k 0*x 0*x 1, k 1*x 10, k 2*x 6, k 3*x 8*x 1, k 4*x 6,
    k 5*x 11*x 2, k 6*x 3, k 7*x 4, k 8*x 4, k 9*x 9*x 1,
    k 10*x 7, k 11*x 8*x 2, k 12*x 5]

/-- Multiply the vector of thirteen fluxes by the stoichiometric matrix. -/
def balance (j : Rates) : State :=
  ![-j 0+j 7+j 12, -j 0+j 2-j 3+j 4-j 9+j 10,
    -j 5+j 7+j 8-j 11+j 12, j 5-j 6, j 6-j 7-j 8, j 11-j 12,
    j 1-j 2+j 3-j 4, j 9-j 10, -j 3+j 4-j 11, j 8-j 9,
    j 0-j 1, j 2-j 5+j 10]

def rhs (k : Rates) (x : State) : State := balance (flux k x)

/-- Total substrate, total kinase, total phosphatase. -/
def totals (x : State) : Totals :=
  ![x 0+x 3+x 4+x 5+x 6+x 7+x 8+x 9+x 10+x 11,
    x 1+x 6+x 7+x 10, x 2+x 3+x 4+x 5]

def project (x : State) : Chart := ![x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11]

def lift (T : Totals) (z : Chart) : State :=
  ![T 0-z 0-z 1-z 2-z 3-z 4-z 5-z 6-z 7-z 8,
    T 1-z 3-z 4-z 7, T 2-z 0-z 1-z 2,
    z 0,z 1,z 2,z 3,z 4,z 5,z 6,z 7,z 8]

def field (k : Rates) (T : Totals) (z : Chart) : Chart := project (rhs k (lift T z))

theorem conserved (k : Rates) (x : State) : totals (rhs k x) = 0 := by
  change totals (balance (flux k x)) = 0
  generalize flux k x = u
  funext i
  fin_cases i <;> dsimp [totals, balance] <;> ring

theorem totals_lift (T : Totals) (z : Chart) : totals (lift T z) = T := by
  funext i
  fin_cases i <;> dsimp [totals, lift] <;> ring

theorem project_lift (T : Totals) (z : Chart) : project (lift T z) = z := by
  funext i
  fin_cases i <;> rfl

theorem lift_project (x : State) : lift (totals x) (project x) = x := by
  funext i
  fin_cases i <;> dsimp [totals, project, lift] <;> ring

theorem equilibrium_iff (k : Rates) (T : Totals) (z : Chart) :
    field k T z = 0 ↔ rhs k (lift T z) = 0 := by
  constructor
  · intro h
    have hz := lift_project (rhs k (lift T z))
    rw [conserved] at hz
    change project (rhs k (lift T z)) = 0 at h
    rw [h] at hz
    rw [← hz]
    funext i
    fin_cases i <;> norm_num [lift]
  · intro h
    unfold field
    rw [h]
    funext i
    fin_cases i <;> rfl

def kinaseProcessivity (k : Rates) : ℝ := k 2/(k 2+k 4)
def phosphataseProcessivity (k : Rates) : ℝ := k 7/(k 7+k 8)

def prescribedRates (p q K δ : ℝ) : Rates :=
  ![K,1,p/δ,1/δ,(1-p)/δ,K,1,q/δ,(1-q)/δ,1/δ,1/δ,1/δ,1/δ]

theorem prescribedRates_pos {p q K δ : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hq : 0 < q) (hq' : q < 1) (hK : 0 < K) (hδ : 0 < δ) :
    ∀ i, 0 < prescribedRates p q K δ i := by
  have h1p := sub_pos.mpr hp'
  have h1q := sub_pos.mpr hq'
  intro i
  fin_cases i <;> dsimp [prescribedRates] <;> first | assumption | positivity

theorem prescribed_processivities {p q K δ : ℝ} (hδ : 0 < δ) :
    kinaseProcessivity (prescribedRates p q K δ) = p ∧
    phosphataseProcessivity (prescribedRates p q K δ) = q := by
  have ratio (x : ℝ) : (x/δ)/(x/δ+(1-x)/δ) = x := by
    rw [← add_div, show x + (1-x) = 1 by ring]
    field_simp
  exact ⟨ratio p, ratio q⟩


/-! The enzyme and substrate critical graphs of the scalar-cubic construction.
Bound coordinates are ordered S00E,S01E,S10E,S11F,S10F,S01F.
Slow coordinates are ordered S11,S01,S10. -/
abbrev Bound := Fin 6 → ℝ
abbrev Slow := Fin 3 → ℝ

def scaledState (η A B C D e f : ℝ) (w : Bound) : State :=
  ![A, η*e, η*f, η*w 3, η*w 4, η*w 5, η*w 1, η*w 2, C, D, η*w 0, B]

def boundAt (x : State) : Bound := ![x 10,x 6,x 7,x 3,x 4,x 5]
def slowAt (x : State) : Slow := ![x 11,x 8,x 9]

def classA (η : ℝ) (y : Slow) (w : Bound) : ℝ :=
  1-y 0-y 1-y 2-η*(w 0+w 1+w 2+w 3+w 4+w 5)
def freeE (w : Bound) : ℝ := 1-w 0-w 1-w 2
def freeF (s : ℝ) (w : Bound) : ℝ := s-w 3-w 4-w 5

def scaledLift (s η : ℝ) (y : Slow) (w : Bound) : State :=
  scaledState η (classA η y w) (y 0) (y 1) (y 2) (freeE w) (freeF s w) w

theorem scaledLift_totals (s η : ℝ) (y : Slow) (w : Bound) :
    totals (scaledLift s η y w) = ![1,η,η*s] := by
  funext i
  fin_cases i <;> dsimp [scaledLift, scaledState, totals, classA, freeE, freeF] <;> ring

/-- Exact six and three right-hand sides after removing the common
physical enzyme factor. No quasisteady substitution has been made. -/
def enzymeRHS (K δ A B C D e f : ℝ) (w : Bound) : Bound :=
  ![K*A*e-w 0, w 0+C*e/δ-w 1/δ, (D*e-w 2)/δ,
    K*B*f-w 3, w 3-w 4/δ, (C*f-w 5)/δ]

def substrateRHS (p q K δ B C D e f : ℝ) (w : Bound) : Slow :=
  ![p*w 1/δ-K*B*f+w 2/δ, (1-p)*w 1/δ-(e+f)*C/δ, (1-q)*w 4/δ-e*D/δ]

theorem exact_split (p q K δ η A B C D e f : ℝ) (w : Bound) :
    let v := rhs (prescribedRates p q K δ) (scaledState η A B C D e f w)
    boundAt v = (fun i => η * enzymeRHS K δ A B C D e f w i) ∧
    slowAt v = (fun i => η * substrateRHS p q K δ B C D e f w i) := by
  constructor <;> funext i <;> fin_cases i <;>
    dsimp [boundAt, slowAt, enzymeRHS, substrateRHS, rhs, flux, balance,
      prescribedRates, scaledState] <;> (try simp only [div_eq_mul_inv]) <;> ring

def enzymeGraph (K δ A B C D e f : ℝ) : Bound :=
  ![K*A*e, δ*K*A*e+C*e, D*e, K*B*f, δ*K*B*f, C*f]

def eDen (K δ A C D : ℝ) : ℝ := 1+(1+δ)*K*A+C+D
def fDen (K δ B C : ℝ) : ℝ := 1+(1+δ)*K*B+C

theorem enzymeGraph_zero {K δ A B C D e f : ℝ} (hδ : δ ≠ 0) :
    enzymeRHS K δ A B C D e f (enzymeGraph K δ A B C D e f) = 0 := by
  funext i
  fin_cases i <;> dsimp [enzymeRHS, enzymeGraph] <;> field_simp <;> ring

theorem enzymeGraph_totals (K δ A B C D e f : ℝ) :
    let w := enzymeGraph K δ A B C D e f
    e+w 0+w 1+w 2 = e*eDen K δ A C D ∧ f+w 3+w 4+w 5 = f*fDen K δ B C := by
  constructor <;> dsimp [enzymeGraph, eDen, fDen] <;> ring

theorem enzymeGraph_free {K δ A B C D s : ℝ} (hE : eDen K δ A C D ≠ 0)
    (hF : fDen K δ B C ≠ 0) :
    let e := 1/eDen K δ A C D
    let f := s/fDen K δ B C
    let w := enzymeGraph K δ A B C D e f
    freeE w = e ∧ freeF s w = f := by
  have eqs := enzymeGraph_totals K δ A B C D (1/eDen K δ A C D) (s/fDen K δ B C)
  dsimp only at eqs ⊢
  obtain ⟨h₁,h₂⟩ := eqs
  rw [div_mul_cancel₀ _ hE] at h₁
  rw [div_mul_cancel₀ _ hF] at h₂
  constructor <;> dsimp only [freeE, freeF] <;> linarith

theorem enzymeGraph_positive {K δ A B C D s : ℝ} (hK : 0 < K) (hδ : 0 < δ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hs : 0 < s) :
    let e := 1/eDen K δ A C D
    let f := s/fDen K δ B C
    0 < e ∧ 0 < f ∧ ∀ i, 0 < enzymeGraph K δ A B C D e f i := by
  dsimp only
  have he : 0 < 1/eDen K δ A C D := by unfold eDen; positivity
  have hf : 0 < s/fDen K δ B C := by unfold fDen; positivity
  refine ⟨he,hf,?_⟩
  intro i
  fin_cases i <;> dsimp [enzymeGraph] <;> positivity

def reduced (p q K A B e f c d : ℝ) : Slow :=
  ![p*(K*A+c)*e - K*B*f + d*e, (1-p)*K*A*e-(p*e+f)*c, (1-q)*K*B*f-e*d]

theorem substrate_on_graph {p q K δ A B e f c d : ℝ} (hδ : δ ≠ 0) :
    substrateRHS p q K δ B (δ*c) (δ*d) e f (enzymeGraph K δ A B (δ*c) (δ*d) e f) =
      reduced p q K A B e f c d := by
  funext i
  fin_cases i <;> dsimp [substrateRHS, enzymeGraph, reduced] <;> field_simp
  all_goals ring

def criticalC (p K A e f : ℝ) : ℝ := (1-p)*K*A*e/(p*e+f)
def criticalD (q K B e f : ℝ) : ℝ := (1-q)*K*B*f/e
def drift (p q K A B e f : ℝ) : ℝ := K*A*e*p*(e+f)/(p*e+f) - q*K*B*f

theorem reduced_on_critical {p q K A B e f : ℝ} (he : e ≠ 0) (hx : p*e+f ≠ 0) :
    reduced p q K A B e f (criticalC p K A e f) (criticalD q K B e f) =
      ![drift p q K A B e f,0,0] := by
  funext i
  fin_cases i <;> dsimp [criticalC, criticalD, drift, reduced] <;> field_simp <;> ring

theorem critical_positive {p q K A B e f : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hq' : q < 1) (hK : 0 < K) (hA : 0 < A) (hB : 0 < B)
    (he : 0 < e) (hf : 0 < f) : 0 < criticalC p K A e f ∧ 0 < criticalD q K B e f := by
  have hp1 := sub_pos.mpr hp'
  have hq1 := sub_pos.mpr hq'
  constructor <;> dsimp [criticalC,criticalD] <;> positivity

/-- Exact increments in the two fast variables when free enzyme levels are
frozen. These are independent of the base point and diagonal. -/
theorem singly_modified_diagonal (p q K A B e f c d x y : ℝ) :
    reduced p q K A B e f (c+x) (d+y) 1 - reduced p q K A B e f c d 1 = -(p*e+f)*x ∧
    reduced p q K A B e f (c+x) (d+y) 2 - reduced p q K A B e f c d 2 = -e*y := by
  constructor <;> dsimp [reduced] <;> ring


/-- Comparison with the scalar flux used in ERK.Scalar. -/
theorem drift_endpoint_formula {p q s K B : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hK : 0 < K) (hB : 0 < B) (hB' : B < 1) :
    drift p q K (1-B) B (1/(1+K*(1-B))) (s/(1+K*B)) =
      K*(1-B)/(1+K*(1-B)) *
        (p*((1+K*B)+s*(1+K*(1-B)))/(p*(1+K*B)+s*(1+K*(1-B)))) -
        q*K*B*s/(1+K*B) := by
  have hA := sub_pos.mpr hB'
  have hu : 0 < 1+K*(1-B) := by positivity
  have hv : 0 < 1+K*B := by positivity
  have hpden : 0 < p*(1+K*B)+s*(1+K*(1-B)) := by positivity
  have hx : 0 < p*(1/(1+K*(1-B)))+s/(1+K*B) := by positivity
  unfold drift
  field_simp

/-- A frozen three-bound-state enzyme field. The two enzymes are obtained
with different choices of binding coefficients and total pool. -/
def frozen (a b c l T : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let e := T-x 0-x 1-x 2
  ![a*e-x 0, x 0+b*e-l*x 1, c*e-l*x 2]

def kinasePart (w : Bound) : Fin 3 → ℝ := ![w 0,w 1,w 2]
def phosphatasePart (w : Bound) : Fin 3 → ℝ := ![w 3,w 4,w 5]

theorem frozen_blocks (K δ A B C D s : ℝ) (w : Bound) :
    let flow := enzymeRHS K δ A B C D (freeE w) (freeF s w) w
    kinasePart flow = frozen (K*A) (C/δ) (D/δ) (1/δ) 1 (kinasePart w) ∧
    phosphatasePart flow = frozen (K*B) 0 (C/δ) (1/δ) s (phosphatasePart w) := by
  constructor <;> funext i <;> fin_cases i <;>
    dsimp [kinasePart,phosphatasePart,enzymeRHS,freeE,freeF,frozen] <;>
    (try simp only [div_eq_mul_inv]) <;> ring

def frozenMatrix {R : Type*} [CommRing R] (a b c l : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of ![![-a-1,-a,-a], ![1-b,-b-l,-b], ![-c,-c,-c-l]]

/-- The Jacobian is the exact linear increment, including terms from the
eliminated free pool. -/
theorem frozen_increment (a b c l T : ℝ) (x h : Fin 3 → ℝ) :
    frozen a b c l T (x+h)-frozen a b c l T x = (frozenMatrix a b c l).mulVec h := by
  funext i
  fin_cases i <;>
    simp [frozen, frozenMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring


/-! The nine-dimensional eta perturbation in (B,c,d,u,v,w,U,V,W). -/
abbrev M := Fin 1 ⊕ Fin 2
abbrev I := M ⊕ Fin 6
def toSlow (δ : ℝ) (y : M → ℝ) : Slow := ![y (.inl 0),δ*y (.inr 0),δ*y (.inr 1)]
def fromSlow (δ : ℝ) (y : Slow) : M → ℝ := Sum.elim (fun _ => y 0) ![y 1/δ,y 2/δ]

def physicalMap (s δ η : ℝ) (x : I → ℝ) : State :=
  scaledLift s η (toSlow δ (x ∘ Sum.inl)) (x ∘ Sum.inr)

def chartMap (δ η : ℝ) (x : I → ℝ) : Chart :=
  let w := x ∘ Sum.inr
  let y := toSlow δ (x ∘ Sum.inl)
  ![η*w 3,η*w 4,η*w 5,η*w 1,η*w 2,y 1,y 2,η*w 0,y 0]

def chartInverse (δ η : ℝ) (z : Chart) : I → ℝ :=
  Sum.elim (fromSlow δ ![z 8,z 5,z 6]) ![z 7/η,z 3/η,z 4/η,z 0/η,z 1/η,z 2/η]

def chartEquiv {δ η : ℝ} (hδ : δ ≠ 0) (hη : η ≠ 0) : (I → ℝ) ≃L[ℝ] Chart :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := chartMap δ η
      invFun := chartInverse δ η
      left_inv := by
        intro x
        funext i
        rcases i with (i|i) | i <;> fin_cases i <;>
          dsimp [chartInverse,chartMap,toSlow,fromSlow] <;> field_simp
      right_inv := by
        intro z
        funext i
        fin_cases i <;> dsimp [chartInverse,chartMap,toSlow,fromSlow] <;> field_simp
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> dsimp [chartMap,toSlow] <;> ring
      map_smul' := by
        intro a x
        funext i
        fin_cases i <;> dsimp [chartMap,toSlow] <;> ring }

@[simp] theorem chartEquiv_apply {δ η : ℝ} (hδ : δ ≠ 0) (hη : η ≠ 0) (x : I → ℝ) :
    chartEquiv hδ hη x = chartMap δ η x := rfl

theorem lift_chartMap (s δ η : ℝ) (x : I → ℝ) :
    lift ![1,η,η*s] (chartMap δ η x) = physicalMap s δ η x := by
  funext i
  fin_cases i <;> dsimp [lift,physicalMap,scaledLift,scaledState,chartMap,freeE,freeF,classA] <;> ring

def etaEq (p q K δ s : ℝ) (tx : ℝ × (I → ℝ)) : I → ℝ :=
  let w := tx.2 ∘ Sum.inr
  let y := toSlow δ (tx.2 ∘ Sum.inl)
  let e := freeE w
  let f := freeF s w
  Sum.elim (fromSlow δ (substrateRHS p q K δ (y 0) (y 1) (y 2) e f w))
    (enzymeRHS K δ (classA tx.1 y w) (y 0) (y 1) (y 2) e f w)

def etaDynamics (p q K δ s η : ℝ) (x : I → ℝ) : I → ℝ :=
  let v := etaEq p q K δ s (η,x)
  Sum.elim (v ∘ Sum.inl) (fun i => v (.inr i)/η)

def stack (y : Slow) (w : Bound) : Chart := ![w 3,w 4,w 5,w 1,w 2,y 1,y 2,w 0,y 0]
theorem project_stack (x : State) : project x = stack (slowAt x) (boundAt x) := rfl

theorem eta_conjugacy {p q K δ s η : ℝ} (hδ : δ ≠ 0) (hη : η ≠ 0) (x : I → ℝ) :
    field (prescribedRates p q K δ) ![1,η,η*s] (chartMap δ η x) =
      η • chartMap δ η (etaDynamics p q K δ s η x) := by
  let w := x ∘ Sum.inr
  let y := toSlow δ (x ∘ Sum.inl)
  let e := freeE w
  let f := freeF s w
  have hs := exact_split p q K δ η (classA η y w) (y 0) (y 1) (y 2) e f w
  unfold field
  rw [lift_chartMap,project_stack]
  change stack (slowAt (rhs _ (scaledState η (classA η y w) (y 0) (y 1) (y 2) e f w)))
    (boundAt (rhs _ (scaledState η (classA η y w) (y 0) (y 1) (y 2) e f w))) = _
  rw [hs.2,hs.1]
  funext i
  fin_cases i <;> dsimp [stack,chartMap,etaDynamics,etaEq,fromSlow,toSlow,w,y,e,f] <;> field_simp

def freeA (y : Slow) : ℝ := 1-y 0-y 1-y 2
def graphE (K δ : ℝ) (y : Slow) : ℝ := 1/eDen K δ (freeA y) (y 1) (y 2)
def graphF (K δ s : ℝ) (y : Slow) : ℝ := s/fDen K δ (y 0) (y 1)
def boundGraph (K δ s : ℝ) (y : Slow) : Bound :=
  enzymeGraph K δ (freeA y) (y 0) (y 1) (y 2) (graphE K δ y) (graphF K δ s y)
def enzymeReduced (p q K δ s : ℝ) (y : Slow) : Slow :=
  substrateRHS p q K δ (y 0) (y 1) (y 2) (graphE K δ y) (graphF K δ s y) (boundGraph K δ s y)
def scaledReduced (p q K δ s : ℝ) (y : M → ℝ) : M → ℝ :=
  fromSlow δ (enzymeReduced p q K δ s (toSlow δ y))
def graphPoint (K δ s : ℝ) (y : M → ℝ) : I → ℝ :=
  Sum.elim y (boundGraph K δ s (toSlow δ y))

theorem enzymeReduced_scaled {p q K δ s : ℝ} (hδ : δ ≠ 0) (y : M → ℝ) :
    let u := toSlow δ y
    enzymeReduced p q K δ s u = reduced p q K (freeA u) (u 0) (graphE K δ u)
      (graphF K δ s u) (y (.inr 0)) (y (.inr 1)) :=
  substrate_on_graph hδ

theorem etaEq_on_graph {p q K δ s : ℝ} (hδ : δ ≠ 0) (y : M → ℝ)
    (hE : eDen K δ (freeA (toSlow δ y)) (toSlow δ y 1) (toSlow δ y 2) ≠ 0)
    (hF : fDen K δ (toSlow δ y 0) (toSlow δ y 1) ≠ 0) :
    etaEq p q K δ s (0, graphPoint K δ s y) = Sum.elim (scaledReduced p q K δ s y) 0 := by
  let u := toSlow δ y
  let w := boundGraph K δ s u
  have hfree : freeE w = graphE K δ u ∧ freeF s w = graphF K δ s u := enzymeGraph_free hE hF
  have ha : classA 0 u w = freeA u := by simp [classA,freeA]
  change Sum.elim (fromSlow δ (substrateRHS p q K δ (u 0) (u 1) (u 2) (freeE w) (freeF s w) w))
    (enzymeRHS K δ (classA 0 u w) (u 0) (u 1) (u 2) (freeE w) (freeF s w) w) = _
  rw [hfree.1,hfree.2,ha]
  exact congrArg (Sum.elim (scaledReduced p q K δ s y)) (enzymeGraph_zero hδ)

end ERK.Model
