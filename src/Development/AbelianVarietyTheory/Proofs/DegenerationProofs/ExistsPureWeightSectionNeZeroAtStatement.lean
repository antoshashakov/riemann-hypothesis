module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_pureWeight_section_ne_zero_at : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) := by
  first | exact @GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at | exact GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at | (intros; apply GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at <;> assumption)
