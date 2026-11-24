module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFundamentalDomainOfExtension
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.existsUnique_prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  first | exact @GlobalTheory.prod_fundamentalDomain_of_extension | exact GlobalTheory.prod_fundamentalDomain_of_extension | (intros; apply GlobalTheory.prod_fundamentalDomain_of_extension <;> assumption)
