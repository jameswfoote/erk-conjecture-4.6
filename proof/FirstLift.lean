import Scalar
import Model
import Lift
import FastSpectrum
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

noncomputable section
open Set Filter Matrix
open scoped Topology
namespace ERK.First

abbrev I3 := Fin 1 ⊕ Fin 2
abbrev Z := I3 → ℝ

def state (b c d : ℝ) : Z := Sum.elim (fun _ => b) ![c,d]
def remaining (δ : ℝ) (y : Z) : ℝ := 1-y (.inl 0)-δ*(y (.inr 0)+y (.inr 1))
def freeE (K δ : ℝ) (y : Z) : ℝ :=
  1 / Model.eDen K δ (remaining δ y) (δ*y (.inr 0)) (δ*y (.inr 1))
def freeF (K s δ : ℝ) (y : Z) : ℝ :=
  s / Model.fDen K δ (y (.inl 0)) (δ*y (.inr 0))

/-- The unscaled three equilibrium constraints, with δ kept as a regular parameter. -/
def constraints (p q K s : ℝ) (u : ℝ × Z) : Z :=
  let (δ,y) := u
  let r := Model.reduced p q K (remaining δ y) (y (.inl 0)) (freeE K δ y)
    (freeF K s δ y) (y (.inr 0)) (y (.inr 1))
  state (r 0) (r 1) (r 2)

/-- The actual vector field in the (B,c,d) chart, where C=δc and D=δd. -/
def dynamics (p q K s δ : ℝ) (y : Z) : Z :=
  let h := constraints p q K s (δ,y)
  state (h (.inl 0)) (h (.inr 0)/δ) (h (.inr 1)/δ)

def e₀ (K b : ℝ) : ℝ := 1/(1+K*(1-b))
def f₀ (K s b : ℝ) : ℝ := s/(1+K*b)
def critical (p q K s b : ℝ) : Z :=
  let e := e₀ K b
  let f := f₀ K s b
  state b (Model.criticalC p K (1-b) e f) (Model.criticalD q K b e f)

theorem fractions_pos {p K s b : ℝ} (hp : 0 < p) (hK : 0 < K) (hs : 0 < s)
    (hb : b ∈ Ioo (0:ℝ) 1) :
    0 < e₀ K b ∧ 0 < f₀ K s b ∧ 0 < p*e₀ K b + f₀ K s b := by
  have ha : 0 < 1-b := sub_pos.mpr hb.2
  have hb' := hb.1
  have he : 0 < e₀ K b := by dsimp [e₀]; positivity
  have hf : 0 < f₀ K s b := by dsimp [f₀]; positivity
  exact ⟨he,hf,by positivity⟩

theorem critical_positive {p q K s b : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hq' : q < 1) (hK : 0 < K) (hs : 0 < s) (hb : b ∈ Ioo (0:ℝ) 1) :
    0 < remaining 0 (critical p q K s b) ∧ ∀ i, 0 < critical p q K s b i := by
  obtain ⟨he,hf,_⟩ := fractions_pos hp hK hs hb
  obtain ⟨hc,hd⟩ := Model.critical_positive hp hp' hq' hK (sub_pos.mpr hb.2) hb.1 he hf
  refine ⟨by simpa [remaining,critical,state] using sub_pos.mpr hb.2,?_⟩
  rintro (i|i)
  · exact hb.1
  · fin_cases i <;> first | exact hc | exact hd

@[simp] theorem remaining_zero (y : Z) : remaining 0 y = 1-y (.inl 0) := by simp [remaining]
@[simp] theorem freeE_zero (K : ℝ) (y : Z) : freeE K 0 y = e₀ K (y (.inl 0)) := by
  simp [freeE,Model.eDen,e₀]
@[simp] theorem freeF_zero (K s : ℝ) (y : Z) : freeF K s 0 y = f₀ K s (y (.inl 0)) := by
  simp [freeF,Model.fDen,f₀]

theorem critical_image {p q K s b : ℝ} (hp : 0 < p) (hK : 0 < K) (hs : 0 < s)
    (hb : b ∈ Ioo (0:ℝ) 1) :
    constraints p q K s (0,critical p q K s b) = state (Scalar.flux p q s K b) 0 0 := by
  obtain ⟨he,hf,hpe⟩ := fractions_pos hp hK hs hb
  have hh := Model.reduced_on_critical (q:=q) (K:=K) (A:=1-b) (B:=b) he.ne' hpe.ne'
  have hd : Model.drift p q K (1-b) b (e₀ K b) (f₀ K s b) = Scalar.flux p q s K b :=
    Model.drift_endpoint_formula hp hs hK hb.1 hb.2
  unfold constraints
  simp only [remaining_zero,freeE_zero,freeF_zero]
  exact (congrArg (fun r : Model.Slow => state (r 0) (r 1) (r 2)) hh).trans (by rw [hd]; rfl)

theorem constraints_smooth {p q K s b : ℝ} (hK : 0 < K) (hb : b ∈ Ioo (0:ℝ) 1)
    (c d : ℝ) : ContDiffAt ℝ 1 (constraints p q K s) (0,state b c d) := by
  have ha : 0 < 1-b := sub_pos.mpr hb.2
  have hb' := hb.1
  have hu : 1 + K*(1-b) ≠ 0 := ne_of_gt (by positivity)
  have hv : 1 + K*b ≠ 0 := ne_of_gt (by positivity)
  apply contDiffAt_pi.mpr
  rintro (i|i)
  · dsimp [constraints,state,Model.reduced,freeE,freeF,Model.eDen,Model.fDen,remaining]
    fun_prop (disch := first | simpa using hu | simpa using hv)
  · fin_cases i <;> dsimp [constraints,state,Model.reduced,freeE,freeF,Model.eDen,Model.fDen,remaining] <;>
      fun_prop (disch := first | simpa using hu | simpa using hv)

theorem two_critical {p q : ℝ} (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1) :
    let s := (1+p)/(2*q)
    ∃ K b₁ b₂ : ℝ, 0 < K ∧ 0 < b₁ ∧ b₁ < b₂ ∧ b₂ < 1 ∧
      ∀ b ∈ ({b₁,b₂} : Set ℝ), constraints p q K s (0,critical p q K s b) = 0 ∧
        (0 < remaining 0 (critical p q K s b) ∧ ∀ i, 0 < critical p q K s b i) ∧
        deriv (Scalar.flux p q s K) b < 0 := by
  let s := (1+p)/(2*q)
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨K,b₁,b₂,hK,h₁,h₁₂,h₂,z₁,z₂,d₁,d₂⟩ := Scalar.two_scalar_sinks p q hp hp' hq
  refine ⟨K,b₁,b₂,hK,h₁,h₁₂,h₂,?_⟩
  intro b hb
  have helper (b : ℝ) (hb : b ∈ Ioo (0:ℝ) 1) (hz : Scalar.flux p q s K b = 0)
      (hd : deriv (Scalar.flux p q s K) b < 0) :
      constraints p q K s (0,critical p q K s b) = 0 ∧
        (0 < remaining 0 (critical p q K s b) ∧ ∀ i, 0 < critical p q K s b i) ∧
        deriv (Scalar.flux p q s K) b < 0 := by
    refine ⟨?_,critical_positive hp hp' hq' hK hs hb,hd⟩
    rw [critical_image hp hK hs hb,hz]
    funext i
    rcases i with i|i
    · rfl
    · fin_cases i <;> rfl
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl|rfl
  · exact helper _ ⟨h₁,h₁₂.trans h₂⟩ z₁ d₁
  · exact helper _ ⟨h₁.trans h₁₂,h₂⟩ z₂ d₂

private theorem state_deriv {b c d : ℝ → ℝ} {b' c' d' t : ℝ}
    (hb : HasDerivAt b b' t) (hc : HasDerivAt c c' t) (hd : HasDerivAt d d' t) :
    HasDerivAt (fun x => state (b x) (c x) (d x)) (state b' c' d') t := by
  apply hasDerivAt_pi.mpr
  rintro (i|i)
  · exact hb
  · fin_cases i <;> first | exact hc | exact hd

theorem critical_smooth {p q K s b : ℝ} (hp : 0 < p) (hK : 0 < K) (hs : 0 < s)
    (hb : b ∈ Ioo (0:ℝ) 1) : ContDiffAt ℝ 1 (critical p q K s) b := by
  obtain ⟨he,hf,hpe⟩ := fractions_pos hp hK hs hb
  have ha : 0 < 1-b := sub_pos.mpr hb.2
  have hb' := hb.1
  have hu : 1 + K*(1-b) ≠ 0 := ne_of_gt (by positivity)
  have hv : 1 + K*b ≠ 0 := ne_of_gt (by positivity)
  apply contDiffAt_pi.mpr
  rintro (i|i)
  · exact contDiffAt_id
  · fin_cases i <;> dsimp [critical,state,Model.criticalC,Model.criticalD,e₀,f₀] <;>
      fun_prop (disch := first | exact hu | exact hv | exact he.ne' | exact hpe.ne')

/-- Derivative of the equilibrium constraints along the two fast coordinate directions. -/
theorem fast_directions {p q K s b : ℝ} (hK : 0 < K) (hb : b ∈ Ioo (0:ℝ) 1)
    (c d v w : ℝ) :
    let H := fun y => constraints p q K s (0,y)
    let e := e₀ K b
    let f := f₀ K s b
    fderiv ℝ H (state b c d) (state 0 v w) =
      state (p*e*v+e*w) (-(p*e+f)*v) (-e*w) := by
  dsimp only
  let H := fun y => constraints p q K s (0,y)
  let base := state b c d
  let move := fun t : ℝ => state b (c+t*v) (d+t*w)
  let rate := state (p*e₀ K b*v+e₀ K b*w) (-(p*e₀ K b+f₀ K s b)*v) (-e₀ K b*w)
  have hpath : HasDerivAt move (state 0 v w) 0 := by
    apply state_deriv (hasDerivAt_const 0 b)
    · simpa using (((hasDerivAt_id' (0:ℝ)).mul_const v).const_add c)
    · simpa using (((hasDerivAt_id' (0:ℝ)).mul_const w).const_add d)
  have hbase : move 0 = base := by simp [base,move]
  have hH : DifferentiableAt ℝ H base :=
    ((constraints_smooth (p:=p) (q:=q) (s:=s) hK hb c d).differentiableAt_one).comp
      base (by fun_prop : DifferentiableAt ℝ (fun y : Z => ((0:ℝ), y)) base)
  have path_eq (t : ℝ) : H (move t) = H base + t • rate := by
    funext i
    rcases i with i|i
    · dsimp [H,base,move,constraints,rate,state,remaining,freeE,freeF,Model.reduced,
        Model.eDen,Model.fDen,e₀,f₀]
      ring
    · fin_cases i <;> dsimp [H,base,move,constraints,rate,state,remaining,freeE,freeF,Model.reduced,
        Model.eDen,Model.fDen,e₀,f₀] <;> ring
  have lhs := hH.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hpath hbase.symm
  have rhs : HasDerivAt (fun t : ℝ => H base + t • rate) rate 0 := by
    simpa using (((hasDerivAt_id' (0:ℝ)).smul_const rate).const_add (H base))
  exact lhs.unique (rhs.congr_of_eventuallyEq (Filter.Eventually.of_forall path_eq))

#print axioms two_critical
#print axioms fast_directions
abbrev Slow1 := Fin 1 → ℝ
abbrev Fast2 := Fin 2 → ℝ

def graph (p q K s : ℝ) (x : Slow1) (i : Fin 2) : ℝ := critical p q K s (x 0) (.inr i)
def scalar (p q K s : ℝ) (x : Slow1) : Slow1 := fun _ => Scalar.flux p q s K (x 0)

theorem join_graph (p q K s : ℝ) (x : Slow1) :
    Sum.elim x (graph p q K s x) = critical p q K s (x 0) := by
  funext i
  rcases i with i|i
  · fin_cases i; rfl
  · rfl

theorem graph_diff {p q K s : ℝ} (x : Slow1) (hp : 0 < p) (hK : 0 < K) (hs : 0 < s)
    (hb : x 0 ∈ Ioo (0:ℝ) 1) : DifferentiableAt ℝ (graph p q K s) x := by
  have ha : 0 < 1-x 0 := sub_pos.mpr hb.2
  have hb' := hb.1
  obtain ⟨he,_,hpe⟩ := fractions_pos hp hK hs hb
  have hu : 1 + K*(1-x 0) ≠ 0 := ne_of_gt (by positivity)
  have hv : 1 + K*x 0 ≠ 0 := ne_of_gt (by positivity)
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [graph,critical,state,Model.criticalC,Model.criticalD,e₀,f₀] <;>
    fun_prop (disch := first | exact hu | exact hv | exact he.ne' | exact hpe.ne')

theorem graph_image {p q K s : ℝ} (x : Slow1) (hp : 0 < p) (hK : 0 < K) (hs : 0 < s)
    (hb : x 0 ∈ Ioo (0:ℝ) 1) :
    ∀ᶠ v in 𝓝 x, constraints p q K s (0,Sum.elim v (graph p q K s v)) =
      Sum.elim (scalar p q K s v) (0:Fast2) := by
  have hnear : ∀ᶠ v in 𝓝 x, v 0 ∈ Ioo (0:ℝ) 1 :=
    (continuous_apply (0:Fin 1)).continuousAt.tendsto.eventually (Ioo_mem_nhds hb.1 hb.2)
  filter_upwards [hnear] with v hv
  rw [join_graph,critical_image hp hK hs hv]
  funext j
  rcases j with j|j
  · rfl
  · fin_cases j <;> rfl

private theorem stateMatrix_at {p q K s b : ℝ} (hK : 0 < K) (hb : b ∈ Ioo (0:ℝ) 1)
    (c d : ℝ) :
    Lift.stateMatrix (constraints p q K s) (0,state b c d) =
      Lift.matrixOf (fderiv ℝ (fun y => constraints p q K s (0,y)) (state b c d)) := by
  let x := state b c d
  have hleft : HasFDerivAt (fun y : Z => ((0:ℝ),y)) (ContinuousLinearMap.inr ℝ ℝ Z) x :=
    (hasFDerivAt_const (0:ℝ) x).prodMk (hasFDerivAt_id x)
  have hh := (constraints_smooth (p:=p) (q:=q) (s:=s) hK hb c d).differentiableAt_one.hasFDerivAt.comp x hleft
  exact congrArg Lift.matrixOf hh.fderiv.symm

theorem frozen_fast {p q K s b : ℝ} (hK : 0 < K) (hb : b ∈ Ioo (0:ℝ) 1) (c d : ℝ) :
    (Lift.stateMatrix (constraints p q K s) (0,state b c d)).toBlocks₂₂ =
      Fast.substrates p (e₀ K b) (f₀ K s b) := by
  let L := fderiv ℝ (fun y => constraints p q K s (0,y)) (state b c d)
  have basis (j : Fin 2) : Pi.single (Sum.inr j) (1:ℝ) =
      state 0 ((Pi.single j 1 : Fin 2 → ℝ) 0) ((Pi.single j 1 : Fin 2 → ℝ) 1) := by
    funext i
    rcases i with i|i
    · simp [state,Pi.single_apply]
    · fin_cases i <;> simp [state,Pi.single_apply]
  have column (j : Fin 2) : L (Pi.single (Sum.inr j) 1) =
      state (p*e₀ K b*((Pi.single j 1 : Fin 2 → ℝ) 0)+e₀ K b*((Pi.single j 1 : Fin 2 → ℝ) 1))
        (-(p*e₀ K b+f₀ K s b)*((Pi.single j 1 : Fin 2 → ℝ) 0)) (-e₀ K b*((Pi.single j 1 : Fin 2 → ℝ) 1)) := by
    rw [basis j]
    exact fast_directions hK hb c d _ _
  rw [stateMatrix_at hK hb c d]
  ext i j : 1
  change Lift.matrixOf L (.inr i) (.inr j) = _
  rw [Lift.matrixOf_apply,column]
  fin_cases i <;> fin_cases j <;> simp [state,Fast.substrates]

theorem fast_hurwitz {p q K s b : ℝ} (hp : 0 < p) (hK : 0 < K) (hs : 0 < s)
    (hb : b ∈ Ioo (0:ℝ) 1) (c d : ℝ) :
    Singular.Hurwitz (Lift.stateMatrix (constraints p q K s) (0,state b c d)).toBlocks₂₂ := by
  obtain ⟨he,hf,_⟩ := fractions_pos hp hK hs hb
  rw [frozen_fast hK hb]
  intro z hz h
  have h' : (z • 1 - Fast.substrates p (e₀ K b) (f₀ K s b)).det = 0 := by
    rw [← neg_sub,Matrix.det_neg,h,mul_zero]
  exact hz.not_gt (Fast.substrates_hurwitz p _ _ hp he hf z h')

theorem scalar_diff {p q K s : ℝ} (x : Slow1) (hd : deriv (Scalar.flux p q s K) (x 0) < 0) :
    DifferentiableAt ℝ (scalar p q K s) x := by
  apply differentiableAt_pi.mpr
  intro i
  exact (differentiableAt_of_deriv_ne_zero hd.ne).comp x (differentiableAt_apply 0 x)

theorem scalar_hurwitz {p q K s b : ℝ} (hd : deriv (Scalar.flux p q s K) b < 0) :
    Singular.Hurwitz (Lift.matrixOf (fderiv ℝ (scalar p q K s) (fun _ => b))) := by
  let x : Slow1 := fun _ => b
  let one : Slow1 := fun _ => 1
  have hconst : HasDerivAt (fun v : ℝ => (fun _ : Fin 1 => v)) one b :=
    hasDerivAt_pi.mpr (fun _ => hasDerivAt_id' b)
  have hfull := (scalar_diff (p:=p) (q:=q) (K:=K) (s:=s) x hd).hasFDerivAt.comp_hasDerivAt b hconst
  have hg : HasDerivAt (fun v : ℝ => scalar p q K s (fun _ => v))
      (fun _ => deriv (Scalar.flux p q s K) b) b :=
    hasDerivAt_pi.mpr (fun _ => (differentiableAt_of_deriv_ne_zero hd.ne).hasDerivAt)
  have heq := hfull.unique hg
  have hs : Pi.single (0:Fin 1) (1:ℝ) = one := by funext i; fin_cases i; simp [one]
  intro z hz hdet
  rw [Matrix.det_fin_one] at hdet
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Lift.matrixOf_apply, hs] at hdet
  change ((fderiv ℝ (scalar p q K s) x one 0 : ℝ) : ℂ) - z = 0 at hdet
  rw [heq] at hdet
  have hr := congrArg Complex.re hdet
  simp at hr
  linarith

theorem dynamics_eq_field (p q K s δ : ℝ) :
    dynamics p q K s δ = Lift.field (constraints p q K s) δ := by
  funext y i
  rcases i with i|i
  · fin_cases i; rfl
  · fin_cases i <;> simp [dynamics,state,Lift.field,Lift.rowMap,div_eq_mul_inv,mul_comm]

#print axioms fast_hurwitz
#print axioms scalar_hurwitz
/-- The actual positive-domain, three-variable vector field is differentiable at finite δ. -/
theorem dynamics_diff {p q K s δ : ℝ} {y : Z} (hK : 0 < K) (hδ : 0 < δ)
    (hA : 0 < remaining δ y) (hy : ∀ i, 0 < y i) :
    DifferentiableAt ℝ (dynamics p q K s δ) y := by
  have hb := hy (.inl 0)
  have hc := hy (.inr 0)
  have hd := hy (.inr 1)
  have hE : Model.eDen K δ (remaining δ y) (δ*y (.inr 0)) (δ*y (.inr 1)) ≠ 0 := by
    unfold Model.eDen; positivity
  have hF : Model.fDen K δ (y (.inl 0)) (δ*y (.inr 0)) ≠ 0 := by unfold Model.fDen; positivity
  apply differentiableAt_pi.mpr
  rintro (i|i)
  · dsimp [dynamics,constraints,state,Model.reduced,freeE,freeF,Model.eDen,Model.fDen,remaining]
    fun_prop (disch := first | exact hE | exact hF)
  · fin_cases i <;> dsimp [dynamics,constraints,state,Model.reduced,freeE,freeF,Model.eDen,Model.fDen,remaining] <;>
      fun_prop (disch := first | exact hE | exact hF | exact hδ.ne')

/-- One branch of the finite δ system, with the actual positive concentrations and strictly
stable three-dimensional Jacobian in the scaled coordinates. -/
theorem positive_stable_branch {p q K s b : ℝ} (hp : 0 < p) (hp' : p < 1) (hq' : q < 1)
    (hK : 0 < K) (hs : 0 < s) (hb : b ∈ Ioo (0:ℝ) 1) (hz : Scalar.flux p q s K b = 0)
    (hd : deriv (Scalar.flux p q s K) b < 0) :
    ∃ u : ℝ → Z, u 0 = critical p q K s b ∧ ContinuousAt u 0 ∧
      ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < remaining δ (u δ) ∧ (∀ i, 0 < u δ i) ∧
        dynamics p q K s δ (u δ) = 0 ∧
        Singular.Hurwitz (Lift.matrixOf (fderiv ℝ (dynamics p q K s δ) (u δ))) := by
  let x : Slow1 := fun _ => b
  let H := constraints p q K s
  let y := critical p q K s b
  have hzero : H (0,y) = 0 := by
    dsimp only [H,y]
    rw [critical_image hp hK hs hb,hz]
    funext i; rcases i with i|i
    · rfl
    · fin_cases i <;> rfl
  have hc : ContDiffAt ℝ 1 H (0,y) := constraints_smooth hK hb _ _
  have hfast : Singular.Hurwitz (Lift.stateMatrix H (0,y)).toBlocks₂₂ := fast_hurwitz hp hK hs hb _ _
  have hey : Sum.elim x (graph p q K s x) = y := join_graph p q K s x
  have hsch := Lift.schur_on_graph H (graph p q K s) (scalar p q K s) x
    (hey.symm ▸ hc.differentiableAt_one) (graph_diff x hp hK hs hb) (scalar_diff x hd)
    (graph_image x hp hK hs hb) (hey.symm ▸ hfast)
  dsimp only at hsch
  rw [hey] at hsch
  have hslow : let J := Lift.stateMatrix H (0,y)
      Singular.Hurwitz (J.toBlocks₁₁ - J.toBlocks₁₂ * J.toBlocks₂₂⁻¹ * J.toBlocks₂₁) := by
    dsimp only; rw [hsch]; exact scalar_hurwitz hd
  obtain ⟨u,hu,huc,huv⟩ := Lift.stable_branch H y hzero hc hfast hslow
  obtain ⟨hA,hyi⟩ := critical_positive hp hp' hq' hK hs hb
  have hcoord (i : I3) : ContinuousAt (fun t => u t i) 0 := (continuous_apply i).continuousAt.comp huc
  have hcont : ContinuousAt (fun t => remaining t (u t)) 0 :=
    (continuousAt_const.sub (hcoord (.inl 0))).sub (continuousAt_id.mul ((hcoord (.inr 0)).add (hcoord (.inr 1))))
  have hAp : ∀ᶠ t in 𝓝 (0:ℝ), 0 < remaining t (u t) :=
    continuousAt_const.eventually_lt hcont (hu ▸ hA)
  have hip : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, 0 < u t i := by
    apply Filter.eventually_all.mpr
    intro i
    exact continuousAt_const.eventually_lt ((continuous_apply i).continuousAt.comp huc) (hu ▸ hyi i)
  refine ⟨u,hu,huc,?_⟩
  filter_upwards [hAp.filter_mono nhdsWithin_le_nhds,hip.filter_mono nhdsWithin_le_nhds,huv]
    with δ ha hi hsol
  rw [dynamics_eq_field]
  exact ⟨ha,hi,hsol.2.1,hsol.2.2⟩

/-- The first singular lift for every prescribed pair. Both positive equilibria use the same
finite K and the same small positive δ, and have strictly ordered free S11 concentrations. -/
theorem two_sinks {p q : ℝ} (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1) :
    let s := (1+p)/(2*q)
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ δ in 𝓝[>] (0:ℝ), ∃ u v : Z, u (.inl 0) < v (.inl 0) ∧
      (∀ y ∈ ({u,v} : Set Z), 0 < remaining δ y ∧ (∀ i, 0 < y i) ∧
        dynamics p q K s δ y = 0 ∧ Singular.Hurwitz (Lift.matrixOf (fderiv ℝ (dynamics p q K s δ) y))) := by
  let s := (1+p)/(2*q)
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨K,b₁,b₂,hK,h₁,h₁₂,h₂,z₁,z₂,d₁,d₂⟩ := Scalar.two_scalar_sinks p q hp hp' hq
  obtain ⟨u,hu,huc,hus⟩ := positive_stable_branch hp hp' hq' hK hs ⟨h₁,h₁₂.trans h₂⟩ z₁ d₁
  obtain ⟨v,hv,hvc,hvs⟩ := positive_stable_branch hp hp' hq' hK hs ⟨h₁.trans h₁₂,h₂⟩ z₂ d₂
  have hord : ∀ᶠ t in 𝓝 (0:ℝ), u t (.inl 0) < v t (.inl 0) :=
    ((continuous_apply _).continuousAt.comp huc).eventually_lt ((continuous_apply _).continuousAt.comp hvc)
      (by change u 0 (.inl 0) < v 0 (.inl 0); rw [hu,hv]; exact h₁₂)
  refine ⟨K,hK,?_⟩
  filter_upwards [hus,hvs,hord.filter_mono nhdsWithin_le_nhds] with δ hsu hsv hov
  refine ⟨u δ,v δ,hov,?_⟩
  intro y hy
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
  rcases hy with rfl|rfl
  · exact hsu
  · exact hsv

#print axioms two_sinks
end ERK.First
