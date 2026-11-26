module
public import Swanepoel.Counting
@[expose] public section

noncomputable section
namespace Swanepoel.TrackSystem

theorem lemma_3_2 (D : TrackSystem) (hq : D.QuadraticBound)
    (A : Finset D.Track) (s : ℤ) (hs : 100 * s ≤ 61 * D.K)
    (hmax : ∀ u ∈ A, (D.s u : ℤ) ≤ s) :
    (D.r : ℤ) + D.defects + (∑ u ∈ A, (D.s u : ℤ)) ≤ N (D.K + A.card) := by
  have hsum : (∑ u ∈ A, (D.s u : ℤ)) ≤ (A.card : ℤ) * s := by
    calc
      (∑ u ∈ A, (D.s u : ℤ)) ≤ ∑ _u ∈ A, s := Finset.sum_le_sum hmax
      _ = (A.card : ℤ) * s := by simp
  have h := low_crossing_bound D.K A.card s ((D.r : ℤ) + D.defects)
    (by positivity) hq hs
  omega

theorem crossing_pair_loss (D : TrackSystem) (h3 : D.NoTriple)
    (hpair : D.CrossingPairBound) (A : Finset D.Track) (hA : A ⊆ D.ordinary)
    (u v : D.Track) (hu : u ∈ A) (hv : v ∈ A) (huv : D.crossing.Adj u v) :
    D.Q A - D.Q ((A.erase u).erase v) ≤ D.K + A.card - 1 := by
  classical
  let B := (A.erase u).erase v
  have huB : u ∉ B := by simp [B]
  have hvB : v ∉ B := by simp [B]
  have hAeq : A = insert u (insert v B) := by
    ext w
    by_cases hwu : w = u
    · subst w; simp [hu]
    by_cases hwv : w = v
    · subst w; simp [hv]
    · simp [B, hwu, hwv]
  have hc : B.card + 2 = A.card := by
    rw [hAeq, Finset.card_insert_of_notMem (by simp [huv.ne, huB]),
      Finset.card_insert_of_notMem hvB]
  have hd : _root_.Disjoint (B.filter (D.crossing.Adj u))
      (B.filter (D.crossing.Adj v)) := by
    apply Finset.disjoint_left.mpr
    intro w huw hvw
    exact h3 u v w huv (Finset.mem_filter.mp hvw).2
      ((Finset.mem_filter.mp huw).2.symm)
  have hdeg : (B.filter (D.crossing.Adj u)).card +
      (B.filter (D.crossing.Adj v)).card ≤ B.card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card (Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hi : D.internal A = D.internal B +
      ((B.filter (D.crossing.Adj u)).card + (B.filter (D.crossing.Adj v)).card) + 1 := by
    rw [hAeq, internal_insert D (insert v B) u (by simp [huv.ne, huB]),
      internal_insert D B v hvB, Finset.filter_insert, ite_eq_left huv,
      Finset.card_insert_of_notMem (by simp [hvB])]
    omega
  have hs : (∑ w ∈ A, (D.s w : ℤ)) =
      (D.s u : ℤ) + D.s v + ∑ w ∈ B, (D.s w : ℤ) := by
    rw [hAeq, Finset.sum_insert (by simp [huv.ne, huB]), Finset.sum_insert hvB]
    ring
  have hp := hpair u (hA hu) v (hA hv) huv
  have hci : (D.internal A : ℤ) ≤ D.internal B + (A.card : ℤ) - 1 := by
    have hh : (D.internal A : ℤ) + 1 ≤ D.internal B + (A.card : ℤ) := by
      exact_mod_cast (show D.internal A + 1 ≤ D.internal B + A.card by omega)
    omega
  change D.Q A - D.Q B ≤ D.K + A.card - 1
  unfold Q
  rw [hs]
  omega

theorem all_subsets_bound (D : TrackSystem) (h3 : D.NoTriple)
    (hpair : D.CrossingPairBound) (hdisjoint : D.DisjointBound)
    (A : Finset D.Track) (hA : A ⊆ D.ordinary) :
    D.Q A + D.defects ≤ N (D.K + A.card) := by
  classical
  revert hA
  refine Finset.strongInductionOn A ?_
  intro A ih hA
  by_cases hd : D.Disjoint A
  · have hz := internal_zero_of_disjoint D A hd
    have h := hdisjoint A hA hd
    unfold Q
    rw [hz]
    simp only [Nat.cast_zero, add_zero]
    convert h using 1; ring
  · simp only [Disjoint, not_forall, not_not] at hd
    obtain ⟨u, hu, v, hv, huv⟩ := hd
    let B := (A.erase u).erase v
    have hBA : B ⊆ A := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hstrict : B ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨hBA, by
      intro h
      have : u ∈ B := h.symm ▸ hu
      simp [B] at this⟩
    have hrec := ih B hstrict (hBA.trans hA)
    have hloss := crossing_pair_loss D h3 hpair A hA u v hu hv huv
    change D.Q A - D.Q B ≤ D.K + A.card - 1 at hloss
    have hc1 := Finset.card_erase_add_one hu
    have hc2 := Finset.card_erase_add_one
      (show v ∈ A.erase u from Finset.mem_erase.mpr ⟨huv.ne', hv⟩)
    have hc : (A.card : ℤ) = (B.card : ℤ) + 2 := by
      dsimp [B]
      omega
    have hx : D.K + (A.card : ℤ) = (D.K + B.card) + 2 := by omega
    rw [hx, N_shift_two]
    omega

theorem Q_all (D : TrackSystem) : D.Q D.ordinary = D.q := by
  classical
  have hd : _root_.Disjoint D.ordinary D.terminal := by
    apply Finset.disjoint_left.mpr
    intro u hu ht
    exact (Finset.mem_sdiff.mp ht).2 hu
  have hU : D.ordinary ∪ D.terminal = Finset.univ := by
    ext u
    simp [terminal]
  have h := internal_union D D.ordinary D.terminal hd
  rw [hU] at h
  have hz : (D.internal Finset.univ : ℤ) = (D.internal D.ordinary : ℤ) +
      D.internal D.terminal + D.crossings D.ordinary D.terminal := by exact_mod_cast h
  have hs : (D.crossings D.ordinary D.terminal : ℤ) =
      ∑ u ∈ D.ordinary, (D.s u : ℤ) := by simp [crossings_sum, s]
  unfold Q q r
  rw [← hs]
  omega

theorem rhombi_bound (D : TrackSystem) (h3 : D.NoTriple)
    (hpair : D.CrossingPairBound) (hdisjoint : D.DisjointBound) :
    (D.q : ℤ) + D.defects ≤ N (D.K + D.t) := by
  have h := all_subsets_bound D h3 hpair hdisjoint D.ordinary (by intro u hu; exact hu)
  simpa [Q_all, t] using h

end Swanepoel.TrackSystem
