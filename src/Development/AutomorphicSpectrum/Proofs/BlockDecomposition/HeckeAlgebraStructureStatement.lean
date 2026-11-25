module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructure
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

theorem _root_.GlobalTheory.T.hecke_algebra_structure : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | exact GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | (intros; apply GlobalTheory.CompanionTheory.HeckeAlg.hk_alg <;> assumption)
