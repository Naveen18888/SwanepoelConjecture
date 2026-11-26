module
public import Swanepoel.ContactFaceCount
public import Mathlib.Analysis.Normed.Module.Connected
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.empty_subdrawing_complement_connected {n : ℕ} (G : PennyGraph n) :
    IsConnected (G.subdrawing ∅)ᶜ := by
  rw [G.subdrawing_empty]
  exact Set.Countable.isConnected_compl_of_one_lt_rank
    (Module.one_lt_rank_of_one_lt_finrank (by norm_num [Plane])) (Set.finite_range G.point).countable

theorem PennyGraph.subdrawingFaces_empty {n : ℕ} (G : PennyGraph n) :
    G.subdrawingFaces ∅={(G.subdrawing ∅)ᶜ} := by
  have hc := G.empty_subdrawing_complement_connected
  ext F
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact Set.mem_singleton_iff.mpr (hc.isPreconnected.connectedComponentIn hx)
  · intro hF
    rw [Set.mem_singleton_iff.mp hF]
    obtain ⟨x,hx⟩ := hc.nonempty
    exact ⟨x,hx,(hc.isPreconnected.connectedComponentIn hx).symm⟩

theorem PennyGraph.subdrawing_face_count_empty {n : ℕ} (G : PennyGraph n) :
    (G.subdrawingFaces ∅).ncard=1 := by rw [G.subdrawingFaces_empty,Set.ncard_singleton]

theorem PennyGraph.subdrawingFaces_univ {n : ℕ} (G : PennyGraph n) :
    G.subdrawingFaces Finset.univ={F : Set Plane | G.IsFace F} := by
  ext F
  simp only [PennyGraph.subdrawingFaces,PennyGraph.IsSubFace,PennyGraph.IsFace,G.subdrawing_univ]

theorem PennyGraph.full_subdrawing_face_count {n : ℕ} (G : PennyGraph n) :
    (G.subdrawingFaces Finset.univ).ncard=Nat.card (PlaneFace G) := by
  rw [G.subdrawingFaces_univ,← Nat.card_coe_set_eq]
  rfl

theorem PennyGraph.subdrawing_face_count_le {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) : (G.subdrawingFaces S).ncard≤S.card+1 := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [G.subdrawing_face_count_empty,Finset.card_empty]
  | @insert e S he ih =>
    rw [G.subdrawing_face_count_insert S e he,Finset.card_insert_of_notMem he]
    split_ifs <;> omega

end Swanepoel
