module
public import Swanepoel.ContactForest
public import Swanepoel.EulerLeaf
public import Swanepoel.EulerAssembly
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.subdrawing_face_count_of_acyclic {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (ha : (G.contactGraph S).IsAcyclic) :
    (G.subdrawingFaces S).ncard=1 := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S=∅
    · subst S
      exact G.subdrawing_face_count_empty
    obtain ⟨e,he,hiso⟩ := G.contact_forest_leaf S ha (Finset.nonempty_iff_ne_empty.mpr hS)
    have hsub : S.erase e ⊆ S := Finset.erase_subset _ _
    have ha' : (G.contactGraph (S.erase e)).IsAcyclic := ha.anti (G.contactGraph_mono hsub)
    have hi := ih (S.erase e) (Finset.erase_ssubset he) ha'
    have hcount : (G.subdrawingFaces (insert e (S.erase e))).ncard=
        (G.subdrawingFaces (S.erase e)).ncard := by
      rcases hiso with hleft | hright
      · exact G.subdrawing_face_count_insert_of_isolated_left _ e (Finset.notMem_erase _ _) hleft
      · exact G.subdrawing_face_count_insert_of_isolated_right _ e (Finset.notMem_erase _ _) hright
    rwa [Finset.insert_erase he,hi] at hcount

theorem PennyGraph.subdrawing_complement_connected_of_acyclic {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (ha : (G.contactGraph S).IsAcyclic) :
    IsConnected (G.subdrawing S)ᶜ := by
  obtain ⟨F,hF⟩ := Set.ncard_eq_one.mp (G.subdrawing_face_count_of_acyclic S ha)
  have hface : G.IsSubFace S F := by
    change F∈G.subdrawingFaces S
    rw [hF]
    exact Set.mem_singleton F
  obtain ⟨x,hx,hFx⟩ := hface
  have hall : (G.subdrawing S)ᶜ ⊆ connectedComponentIn (G.subdrawing S)ᶜ x := by
    intro z hz
    have hc : connectedComponentIn (G.subdrawing S)ᶜ z ∈ G.subdrawingFaces S := ⟨z,hz,rfl⟩
    rw [hF] at hc
    have heq := (Set.mem_singleton_iff.mp hc).trans hFx
    rw [← heq]
    exact mem_connectedComponentIn hz
  have heq : (G.subdrawing S)ᶜ=connectedComponentIn (G.subdrawing S)ᶜ x :=
    hall.antisymm (connectedComponentIn_subset _ _)
  exact ⟨⟨x,hx⟩,heq ▸ isPreconnected_connectedComponentIn⟩

theorem PennyGraph.boundedFace_count_eq_zero_of_acyclic {n : ℕ} (G : PennyGraph n)
    (ha : G.graph.IsAcyclic) : Fintype.card (BoundedFace G)=0 := by
  have h := G.subdrawing_face_count_of_acyclic Finset.univ
    (by simpa only [G.contactGraph_univ] using ha)
  rw [G.full_subdrawing_face_count,G.all_face_count] at h
  omega

theorem PennyGraph.faceEuler_of_isTree {n : ℕ} (G : PennyGraph n)
    (ht : G.graph.IsTree) : G.FaceEuler := by
  classical
  have hm := ht.card_edgeFinset
  have hmi : G.edgeCount+1=n := by
    simpa only [PennyGraph.edgeCount,Fintype.card_fin] using hm
  have hf := G.boundedFace_count_eq_zero_of_acyclic ht.isAcyclic
  unfold PennyGraph.FaceEuler
  rw [hf]
  omega

theorem PennyGraph.faceEuler_of_cycle_separation {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected)
    (hcycle : ∀ S : Finset (ContactEdge G), ∀ e : ContactEdge G, e∉S →
      (G.contactGraph S).Reachable e.val.1 e.val.2 → ¬G.SameInsertionSides S e) :
    G.FaceEuler :=
  G.faceEuler_of_forest_and_cycle_separation hc G.subdrawing_face_count_of_acyclic hcycle

theorem PennyGraph.faceEuler_of_connected_cycle_separation {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected)
    (hcycle : ∀ S : Finset (ContactEdge G), (G.contactGraph S).Connected →
      ∀ e : ContactEdge G, e∉S → ¬G.SameInsertionSides S e) : G.FaceEuler := by
  obtain ⟨T,hT,hcard⟩ := G.exists_contact_spanning_tree hc
  apply G.faceEuler_of_tree_insertion T hcard
    (G.subdrawing_face_count_of_acyclic T hT.isAcyclic)
  intro S hTS e he
  exact hcycle S (hT.connected.mono (G.contactGraph_mono hTS)) e he

theorem PennyGraph.euler_with_defects_of_connected_cycle_separation {n : ℕ}
    (G : PennyGraph n) (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcycle : ∀ S : Finset (ContactEdge G), (G.contactGraph S).Connected →
      ∀ e : ContactEdge G, e∉S → ¬G.SameInsertionSides S e) :
    (n : ℤ)-G.edgeCount+(Fintype.card (RhombusSet G)+G.faceDefectCount ht)=1 :=
  G.euler_with_defects ht (G.faceEuler_of_connected_cycle_separation hc hcycle)

end Swanepoel
