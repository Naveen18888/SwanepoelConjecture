module
public import Swanepoel.LeafTrackTransfer
public import Swanepoel.FacePortLowerBound
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.componentIsolatedDeletion {n m : ℕ}
    (G : PennyGraph n) (H : PennyGraph m) (htG : G.TriangleFree) (htH : H.TriangleFree)
    (l : TrackComponent G) (f : TrackComponent H→TrackComponent G)
    (hf : Function.Injective f)
    (himage : Finset.univ.image f=Finset.univ.erase l)
    (hcross : ∀ c d,ComponentCrosses c d↔ComponentCrosses (f c) (f d))
    (hterminal : ∀ c,c∈H.terminalTrackComponents↔f c∈G.terminalTrackComponents)
    (hdefects : H.faceDefectCount htH=G.faceDefectCount htG)
    (hisolated : ∀ c,¬ComponentCrosses l c) :
    TrackSystem.IsolatedDeletion
      (componentSystem G htG G.ordinaryTrackComponents (G.faceDefectCount htG))
      (componentSystem H htH H.ordinaryTrackComponents (H.faceDefectCount htH)) := by
  let EG := Fintype.equivFin (TrackComponent G)
  let EH := Fintype.equivFin (TrackComponent H)
  let f' : Fin (Fintype.card (TrackComponent H))→Fin (Fintype.card (TrackComponent G)) :=
    fun u => EG (f (EH.symm u))
  have hne (c : TrackComponent H) : f c≠l := by
    have hc : f c∈Finset.univ.image f :=
      Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩
    rw [himage] at hc
    exact (Finset.mem_erase.mp hc).1
  refine {
    leaf := EG l
    map := f'
    injective := EG.injective.comp (hf.comp EH.symm.injective)
    image_univ := ?_
    crossing := ?_
    terminal := ?_
    defects := hdefects
    isolated := ?_
  }
  · change (Finset.univ : Finset (Fin (Fintype.card (TrackComponent H)))).image f'=
      (Finset.univ : Finset (Fin (Fintype.card (TrackComponent G)))).erase (EG l)
    ext i
    constructor
    · intro hi
      obtain ⟨u,_hu,rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_univ _⟩
      intro heq
      exact hne (EH.symm u) (EG.injective heq)
    · intro hi
      have h := Finset.mem_erase.mp hi
      have hm : EG.symm i∈Finset.univ.image f := by
        rw [himage]
        apply Finset.mem_erase.mpr
        refine ⟨?_,Finset.mem_univ _⟩
        intro heq
        apply h.1
        calc
          i=EG (EG.symm i) := (EG.apply_symm_apply i).symm
          _=EG l := congrArg EG heq
      obtain ⟨c,_hc,hfc⟩ := Finset.mem_image.mp hm
      refine Finset.mem_image.mpr ⟨EH c,Finset.mem_univ _,?_⟩
      dsimp only [f']
      rw [EH.symm_apply_apply,hfc,EG.apply_symm_apply]
  · intro u v
    change ComponentCrosses (EH.symm u) (EH.symm v)↔
      ComponentCrosses (EG.symm (f' u)) (EG.symm (f' v))
    simpa only [f',Equiv.symm_apply_apply] using hcross (EH.symm u) (EH.symm v)
  · change ∀ u : Fin (Fintype.card (TrackComponent H)),
      u∈(Finset.univ : Finset (Fin (Fintype.card (TrackComponent H))))\
        H.ordinaryTrackComponents.map EH.toEmbedding↔
      f' u∈(Finset.univ : Finset (Fin (Fintype.card (TrackComponent G))))\
        G.ordinaryTrackComponents.map EG.toEmbedding
    intro u
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_map_equiv]
    simpa only [H.mem_terminalTrackComponents,G.mem_terminalTrackComponents,f',
      Equiv.symm_apply_apply] using hterminal (EH.symm u)
  · intro i hi
    change ComponentCrosses (EG.symm (EG l)) (EG.symm i) at hi
    rw [EG.symm_apply_apply] at hi
    exact hisolated _ hi

theorem PennyGraph.disjoint_bound_of_component_erase_isolated {n m : ℕ}
    (G : PennyGraph n) (H : PennyGraph m) (htG : G.TriangleFree) (htH : H.TriangleFree)
    (l : TrackComponent G) (f : TrackComponent H→TrackComponent G)
    (hf : Function.Injective f)
    (himage : Finset.univ.image f=Finset.univ.erase l)
    (hcross : ∀ c d,ComponentCrosses c d↔ComponentCrosses (f c) (f d))
    (hterminal : ∀ c,c∈H.terminalTrackComponents↔f c∈G.terminalTrackComponents)
    (hdefects : H.faceDefectCount htH=G.faceDefectCount htG)
    (hisolated : ∀ c,¬ComponentCrosses l c)
    (hrec : (componentSystem H htH H.ordinaryTrackComponents (H.faceDefectCount htH)).DisjointBound) :
    (componentSystem G htG G.ordinaryTrackComponents (G.faceDefectCount htG)).DisjointBound :=
  (G.componentIsolatedDeletion H htG htH l f hf himage hcross hterminal hdefects hisolated).disjointBound
    (H.canonical_componentSystem_K_nonneg htH) hrec

end Swanepoel
