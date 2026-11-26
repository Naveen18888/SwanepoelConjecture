module
public import Swanepoel.Tracks
@[expose] public section

noncomputable section
namespace Swanepoel.TrackSystem
attribute [local instance] Classical.propDecidable

def edgeWeight (D : TrackSystem) (u v : D.Track) : ℕ := by
  classical
  exact if u < v ∧ D.crossing.Adj u v then 1 else 0

theorem internal_sum (D : TrackSystem) (A : Finset D.Track) :
    D.internal A = ∑ u ∈ A, ∑ v ∈ A, D.edgeWeight u v := by
  classical
  simp only [internal, edgeWeight, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.product_eq_sprod, Finset.sum_product]

theorem edgeWeight_pair (D : TrackSystem) (u v : D.Track) (hne : u ≠ v) :
    D.edgeWeight u v + D.edgeWeight v u = if D.crossing.Adj u v then 1 else 0 := by
  classical
  rcases lt_or_gt_of_ne hne with h | h <;>
    simp [edgeWeight, h, not_lt_of_ge (le_of_lt h), D.crossing.adj_comm]

theorem internal_insert (D : TrackSystem) (A : Finset D.Track) (u : D.Track)
    (hu : u ∉ A) :
    D.internal (insert u A) = D.internal A + (A.filter (D.crossing.Adj u)).card := by
  classical
  have hp : (∑ v ∈ A, D.edgeWeight u v) + (∑ v ∈ A, D.edgeWeight v u) =
      (A.filter (D.crossing.Adj u)).card := by
    rw [← Finset.sum_add_distrib]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    exact edgeWeight_pair D u v (by intro h; exact hu (h ▸ hv))
  simp only [internal_sum, Finset.sum_insert hu]
  simp only [edgeWeight, lt_self_iff_false, false_and, ite_false, zero_add] at *
  rw [Finset.sum_add_distrib]
  omega

theorem crossings_sum (D : TrackSystem) (A B : Finset D.Track) :
    D.crossings A B = ∑ u ∈ A, (B.filter (D.crossing.Adj u)).card := by
  classical
  simp only [crossings, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.product_eq_sprod, Finset.sum_product]

theorem internal_union (D : TrackSystem) (A B : Finset D.Track)
    (hAB : _root_.Disjoint A B) :
    D.internal (A ∪ B) = D.internal A + D.internal B + D.crossings A B := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [internal_sum, crossings_sum]
  | @insert u A hu ih =>
    have huB : u ∉ B := (Finset.disjoint_insert_left.mp hAB).1
    have hd : _root_.Disjoint A B := (Finset.disjoint_insert_left.mp hAB).2
    have hf : _root_.Disjoint (A.filter (D.crossing.Adj u)) (B.filter (D.crossing.Adj u)) :=
      hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [Finset.insert_union, internal_insert D (A ∪ B) u (by simp [hu, huB]),
      ih hd, internal_insert D A u hu, Finset.filter_union,
      Finset.card_union_of_disjoint hf]
    simp only [crossings_sum, Finset.sum_insert hu]
    omega

theorem internal_zero_of_disjoint (D : TrackSystem) (A : Finset D.Track)
    (hA : D.Disjoint A) : D.internal A = 0 := by
  classical
  rw [internal_sum]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  simp [edgeWeight, hA u hu v hv]

end Swanepoel.TrackSystem
