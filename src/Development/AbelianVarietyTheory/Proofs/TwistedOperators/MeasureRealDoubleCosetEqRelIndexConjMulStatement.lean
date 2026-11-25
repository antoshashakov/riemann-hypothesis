module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMul
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  first | exact @GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | exact GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | (intros; apply GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul <;> assumption)
