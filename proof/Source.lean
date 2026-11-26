import Model

noncomputable section
namespace ERK.Source
open Model

/-- Equation (4) of Conradi, Obatake, Shiu & Tang, with zero-based indices.
The factors are written in the paper's order, independently of the flux table. -/
def equation4 (k : Rates) (x : State) : State :=
  ![-k 0*x 0*x 1+k 7*x 4+k 12*x 5,
    -k 0*x 0*x 1-k 3*x 1*x 8-k 9*x 9*x 1+k 2*x 6+k 4*x 6+k 10*x 7,
    -k 5*x 2*x 11-k 11*x 2*x 8+k 7*x 4+k 8*x 4+k 12*x 5,
    k 5*x 2*x 11-k 6*x 3,
    k 6*x 3-k 7*x 4-k 8*x 4,
    k 11*x 2*x 8-k 12*x 5,
    k 3*x 1*x 8+k 1*x 10-k 2*x 6-k 4*x 6,
    k 9*x 9*x 1-k 10*x 7,
    -k 3*x 1*x 8-k 11*x 2*x 8+k 4*x 6,
    -k 9*x 9*x 1+k 8*x 4,
    k 0*x 0*x 1-k 1*x 10,
    -k 5*x 2*x 11+k 2*x 6+k 10*x 7]

theorem reaction_model_eq_equation4 (k : Rates) (x : State) : rhs k x = equation4 k x := by
  funext i
  fin_cases i <;> dsimp [rhs,balance,flux,equation4] <;> ring

/-- A linear right inverse after dropping the first three conserved coordinates.
Stoichiometric displacements allow signed coefficients of reaction vectors. -/
def displacement (z : Chart) : Rates :=
  ![z 7+z 3+z 8,z 3+z 8,z 8,0,0,0,-z 0,-z 0-z 6-z 4-z 1,z 6+z 4,z 4,0,-z 5,-z 5-z 2]

theorem project_displacement (z : Chart) : project (balance (displacement z)) = z := by
  funext i
  fin_cases i <;> dsimp [project,balance,displacement] <;> ring

theorem totals_balance (j : Rates) : totals (balance j) = 0 := by
  funext i
  fin_cases i <;> dsimp [totals,balance] <;> ring

theorem totals_sub (x y : State) : totals (x-y) = totals x - totals y := by
  funext i
  fin_cases i <;> dsimp [totals] <;> ring

/-- The three total equations (5) define the entire affine stoichiometric
compatibility space. Intersecting with positive concentrations gives its physical interior. -/
theorem same_class_iff (x y : State) :
    totals x = totals y ↔ ∃ j : Rates, y-x = balance j := by
  constructor
  · intro ht
    let z := project (y-x)
    have hzero : totals (y-x) = 0 := by rw [totals_sub,ht,sub_self]
    refine ⟨displacement z, ?_⟩
    calc y-x = lift (totals (y-x)) z := (lift_project _).symm
         _ = lift (totals (balance (displacement z))) (project (balance (displacement z))) := by
           rw [totals_balance,project_displacement,hzero]
         _ = _ := lift_project _
  · rintro ⟨j,hj⟩
    have h := congrArg totals hj
    rw [totals_sub,totals_balance,sub_eq_zero] at h
    exact h.symm

theorem class_dimension : Module.finrank ℝ Chart = 9 := by simp [Chart]

#print axioms reaction_model_eq_equation4
#print axioms same_class_iff
#print axioms class_dimension
end ERK.Source
