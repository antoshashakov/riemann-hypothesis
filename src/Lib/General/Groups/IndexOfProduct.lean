import Lib.Base

/-! Known result: the index of a product of subgroups in a finite product of groups is the product
of the indices (an infinite index is read as `0`). Mathlib's `Subgroup.index_pi` is the case where
all the factors are the same group. -/

/-- In a finite product of groups `G i`, the index of the product `∏ i, H i` of subgroups
`H i ≤ G i` is the product of the indices of the `H i`. An infinite index is read as `0`. -/
lemma New.Seesaw.index_pi_univ {I : Type*} {G : I → Type*} [Fintype I] [∀ i : I, Group (G i)]
    (H : ∀ i : I, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i : I, (H i).index :=
  (Nat.card_congr (QuotientGroup.leftRel_pi H ▸ Setoid.piQuotientEquiv _) ▸ Nat.card_pi :)
