module
public import Swanepoel.ContactGraph
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.SameInsertionSides {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) : Prop :=
  connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2))=
    connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2))

theorem PennyGraph.face_count_insert_of_same_sides {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    (hs : G.SameInsertionSides S e) :
    (G.subdrawingFaces (insert e S)).ncard=(G.subdrawingFaces S).ncard := by
  unfold PennyGraph.SameInsertionSides at hs
  rw [G.subdrawing_face_count_insert S e he,ite_eq_left hs,add_zero]

theorem PennyGraph.face_count_insert_of_separate_sides {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    (hs : ¬G.SameInsertionSides S e) :
    (G.subdrawingFaces (insert e S)).ncard=(G.subdrawingFaces S).ncard+1 := by
  unfold PennyGraph.SameInsertionSides at hs
  rw [G.subdrawing_face_count_insert S e he,ite_eq_right hs]

theorem PennyGraph.face_count_union_of_separating {n : ℕ} (G : PennyGraph n)
    (T R : Finset (ContactEdge G)) (hTR : _root_.Disjoint T R)
    (hsep : ∀ S : Finset (ContactEdge G), T ⊆ S →
      ∀ e : ContactEdge G, e∉S → ¬G.SameInsertionSides S e) :
    (G.subdrawingFaces (T ∪ R)).ncard=(G.subdrawingFaces T).ncard+R.card := by
  classical
  induction R using Finset.induction_on with
  | empty => simp
  | @insert e R he ih =>
    have heT : e∉T := (Finset.disjoint_insert_right.mp hTR).1
    have hdis : _root_.Disjoint T R := (Finset.disjoint_insert_right.mp hTR).2
    have heU : e∉T ∪ R := by simp [heT,he]
    rw [Finset.union_insert,G.face_count_insert_of_separate_sides (T ∪ R) e heU
      (hsep (T ∪ R) Finset.subset_union_left e heU),ih hdis,
      Finset.card_insert_of_notMem he]
    omega

theorem PennyGraph.faceEuler_of_tree_insertion {n : ℕ} (G : PennyGraph n)
    (T : Finset (ContactEdge G)) (hcard : T.card+1=n)
    (hbase : (G.subdrawingFaces T).ncard=1)
    (hsep : ∀ S : Finset (ContactEdge G), T ⊆ S →
      ∀ e : ContactEdge G, e∉S → ¬G.SameInsertionSides S e) : G.FaceEuler := by
  classical
  have hdis : _root_.Disjoint T (Finset.univ \ T) := by
    exact Finset.disjoint_left.mpr (fun e he hdiff => (Finset.mem_sdiff.mp hdiff).2 he)
  have hf := G.face_count_union_of_separating T (Finset.univ \ T) hdis hsep
  have hU : T ∪ (Finset.univ \ T)=Finset.univ := by ext e; simp
  rw [hU,G.full_subdrawing_face_count,hbase,Finset.card_sdiff_of_subset (Finset.subset_univ T),
    Finset.card_univ,G.contactEdge_count] at hf
  have hTle : T.card≤G.edgeCount := by
    rw [← G.contactEdge_count,← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ T)
  apply G.faceEuler_iff_all_faces.mpr
  have hfi : (Nat.card (PlaneFace G) : ℤ)=1+((G.edgeCount : ℤ)-T.card) := by
    simp only [hf,Nat.cast_add,Nat.cast_one,Nat.cast_sub hTle]
  omega

theorem PennyGraph.faceEuler_of_forest_and_cycle_separation {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected)
    (hforest : ∀ T : Finset (ContactEdge G), (G.contactGraph T).IsAcyclic →
      (G.subdrawingFaces T).ncard=1)
    (hcycle : ∀ S : Finset (ContactEdge G), ∀ e : ContactEdge G, e∉S →
      (G.contactGraph S).Reachable e.val.1 e.val.2 → ¬G.SameInsertionSides S e) :
    G.FaceEuler := by
  obtain ⟨T,hT,hcard⟩ := G.exists_contact_spanning_tree hc
  apply G.faceEuler_of_tree_insertion T hcard (hforest T hT.isAcyclic)
  intro S hTS e he
  exact hcycle S e he ((hT.connected e.val.1 e.val.2).mono (G.contactGraph_mono hTS))

end Swanepoel
