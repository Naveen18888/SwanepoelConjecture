module
public import Swanepoel.EdgePartition
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

structure VertexSplit {n : ℕ} (G : PennyGraph n) where
  left : Finset (Fin n)
  right : Finset (Fin n)
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  left_smaller : left.card < n
  right_smaller : right.card < n
  edges : G.edgeCount = (G.restrict left).edgeCount + (G.restrict right).edgeCount
  sizes : left.card + right.card = n ∨ left.card + right.card = n+1

theorem card_lt_of_missing {n : ℕ} (S : Finset (Fin n)) (v : Fin n) (hv : v ∉ S) :
    S.card < n := by
  have hs : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, by
    intro h
    exact hv (h.symm ▸ Finset.mem_univ v)⟩
  simpa using Finset.card_lt_card hs

theorem disconnected_split {n : ℕ} (G : PennyGraph n) (hn : 1 ≤ n)
    (hG : ¬ G.graph.Connected) : Nonempty (VertexSplit G) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨S, hs, ht, hsep⟩ := finite_graph_separation G.graph hG
  let T := Finset.univ \ S
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  have hcover : S ∪ T = Finset.univ := by ext w; simp [T]
  have hinter : S ∩ T = ∅ := by ext w; simp [T]
  have he := induced_edge_partition G.graph S T hcover
    (by intro u hu hut; exact False.elim ((Finset.mem_sdiff.mp hut).2 hu))
    (by intro u hu _ v hv _; exact hsep u hu v (Finset.mem_sdiff.mp hv).2)
  have hc := Finset.card_union_add_card_inter S T
  rw [hcover, hinter] at hc
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty, add_zero] at hc
  refine ⟨⟨S, T, ⟨a, ha⟩, ⟨b, hb⟩,
    card_lt_of_missing S b (Finset.mem_sdiff.mp hb).2,
    card_lt_of_missing T a (by simp [T, ha]), ?_, Or.inl hc.symm⟩⟩
  rw [G.restrict_edgeCount S, G.restrict_edgeCount T]
  simpa only [PennyGraph.edgeCount, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] using he

theorem cut_vertex_split {n : ℕ} (G : PennyGraph n) (hn : 3 ≤ n) (v : Fin n)
    (hv : ¬ (G.graph.induce {w | w ≠ v}).Connected) : Nonempty (VertexSplit G) := by
  classical
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : Nonempty (↑({w : Fin n | w ≠ v}) : Type) := by
    obtain ⟨w, hw⟩ := exists_ne v
    exact ⟨⟨w, hw⟩⟩
  obtain ⟨U, hu, hw, hsepU⟩ := finite_graph_separation (G.graph.induce {w | w ≠ v}) hv
  let S : Finset (Fin n) := Finset.univ.filter
    (fun w => w = v ∨ ∃ h : w ≠ v, (⟨w, h⟩ : {w : Fin n // w ≠ v}) ∈ U)
  let T : Finset (Fin n) := Finset.univ.filter
    (fun w => w = v ∨ ∃ h : w ≠ v, (⟨w, h⟩ : {w : Fin n // w ≠ v}) ∉ U)
  have hS (w : Fin n) (h : w ≠ v) :
      w ∈ S ↔ (⟨w, h⟩ : {w : Fin n // w ≠ v}) ∈ U := by simp [S, h]
  have hT (w : Fin n) (h : w ≠ v) :
      w ∈ T ↔ (⟨w, h⟩ : {w : Fin n // w ≠ v}) ∉ U := by simp [T, h]
  have hvS : v ∈ S := by simp [S]
  have hvT : v ∈ T := by simp [T]
  have hcover : S ∪ T = Finset.univ := by
    ext w
    by_cases h : w = v
    · subst w; simp [hvS]
    · simp only [Finset.mem_union, Finset.mem_univ, iff_true, hS w h, hT w h]
      exact Classical.em _
  have hinter : S ∩ T = {v} := by
    ext w
    by_cases h : w = v
    · subst w; simp [hvS, hvT]
    · simp only [Finset.mem_inter, Finset.mem_singleton, hS w h, hT w h]
      simp [h]
  have hover : ∀ u ∈ S, u ∈ T → ∀ w ∈ S, w ∈ T → u = w := by
    intro u hu hut w hw hwt
    have hu' : u = v := by simpa [hinter] using (Finset.mem_inter.mpr ⟨hu, hut⟩)
    have hw' : w = v := by simpa [hinter] using (Finset.mem_inter.mpr ⟨hw, hwt⟩)
    exact hu'.trans hw'.symm
  have hsep : ∀ u ∈ S, u ∉ T → ∀ w ∈ T, w ∉ S → ¬ G.graph.Adj u w := by
    intro u hu hut w hw hws
    have huv : u ≠ v := by intro h; exact hut (h.symm ▸ hvT)
    have hwv : w ≠ v := by intro h; exact hws (h.symm ▸ hvS)
    exact hsepU ⟨u, huv⟩ ((hS u huv).mp hu) ⟨w, hwv⟩ ((hT w hwv).mp hw)
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hw
  have hnotS : b.val ∉ S := by
    rw [hS b.val b.property]
    exact (Finset.mem_sdiff.mp hb).2
  have hnotT : a.val ∉ T := by
    rw [hT a.val a.property]
    exact not_not.mpr ha
  have he := induced_edge_partition G.graph S T hcover hover hsep
  have hc := Finset.card_union_add_card_inter S T
  rw [hcover, hinter] at hc
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hc
  refine ⟨⟨S, T, ⟨v, hvS⟩, ⟨v, hvT⟩,
    card_lt_of_missing S b.val hnotS, card_lt_of_missing T a.val hnotT,
    ?_, Or.inr hc.symm⟩⟩
  rw [G.restrict_edgeCount S, G.restrict_edgeCount T]
  simpa only [PennyGraph.edgeCount, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] using he

end Swanepoel
