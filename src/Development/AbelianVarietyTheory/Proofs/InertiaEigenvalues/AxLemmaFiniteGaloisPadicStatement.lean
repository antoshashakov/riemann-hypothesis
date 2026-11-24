module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.axLemma_finiteGalois_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  first | exact @GlobalTheory.PMon.Ram.axIn_padic | exact GlobalTheory.PMon.Ram.axIn_padic | (intros; apply GlobalTheory.PMon.Ram.axIn_padic <;> assumption)
