module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixing
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.normal_subgroup_le_unramified_fixing : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), NS Ω S ≤ (maxUnramifiedOutside (F := F) (Ω := Ω) S).fixingSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | exact GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup <;> assumption)
