module

public import Formalism.ConjugateSelfDual.Statement
public import Formalism.CyclotomicNorms.StatementT
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgClosedResidueField
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.ResidueBar

theorem residueField_ringEquiv_fbar : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  first
  | exact @_root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv
  | exact _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv
  | (apply _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv ..)

end GlobalTheory.ResidueBar
