module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassGroupIdelicFiniteIndex
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open IsDedekindDomain NumberField

theorem _root_.GlobalTheory.T.rayClassGroup_idelic_finiteIndex : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite → ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ GlobalTheory.LevelChars.levSub L S N).FiniteIndex := by
  first | exact @GlobalTheory.LevelChars.rayClass_finite | exact GlobalTheory.LevelChars.rayClass_finite | (intros; apply GlobalTheory.LevelChars.rayClass_finite <;> assumption)
