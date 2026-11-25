module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusJacobianDet
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.torus_jacobian_det : ∀ {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  first | exact @GlobalTheory.CompanionTheory.Cone.dlog_ratio_det | exact GlobalTheory.CompanionTheory.Cone.dlog_ratio_det | (intros; apply GlobalTheory.CompanionTheory.Cone.dlog_ratio_det <;> assumption)
