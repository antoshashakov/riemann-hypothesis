module

public import Mathlib.MeasureTheory.Group.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AddFundamentalDomainMeasureEqOfCountable
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

theorem _root_.GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  first | exact @GlobalTheory.addFundamentalDomains_measure_eq | exact GlobalTheory.addFundamentalDomains_measure_eq | (intros; apply GlobalTheory.addFundamentalDomains_measure_eq <;> assumption)
