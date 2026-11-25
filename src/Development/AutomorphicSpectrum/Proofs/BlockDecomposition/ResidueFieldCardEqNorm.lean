module

public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Formalism.ConjugateSelfDual.Statement
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.LocRes

theorem natCard_residueField_eq_normV : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Nat.card 𝓀[v.adicCompletion F] = normV v := by
  intro F _ _ v
  rw [GroundTheory.Global.natCard_residueField_adicCompletion v, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

end GlobalTheory.CompanionTheory.LocRes
