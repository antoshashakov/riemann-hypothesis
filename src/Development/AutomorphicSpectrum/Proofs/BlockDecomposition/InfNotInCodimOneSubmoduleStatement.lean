module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmodule
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inf_not_in_codim_one_submodule : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (T : Submodule ℂ V), Module.rank ℂ (V ⧸ T) ≤ 1 → ∀ A C : Subrepresentation ρ, (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T → ¬ A.toSubmodule ≤ T → ¬ C.toSubmodule ≤ T → ¬ (A ⊓ C).toSubmodule ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | exact GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | (intros; apply GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet <;> assumption)
