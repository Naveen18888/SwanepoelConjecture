module
public import Swanepoel.TrackClassification
public import Swanepoel.DefectFree
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.defectPlaneFaces_eq_empty_of_defect_free {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hf : G.faceDefectCount ht=0) : G.defectPlaneFaces ht=∅ := by
  apply Finset.card_eq_zero.mp
  rwa [G.defectPlaneFaces_card ht]

theorem PennyGraph.terminalTrackComponents_eq_empty_of_defect_free {n : ℕ}
    (G : PennyGraph n) (ht : G.TriangleFree) (hf : G.faceDefectCount ht=0) :
    G.terminalTrackComponents=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨e,_,_,he⟩ := (G.terminal_iff_defect_source ht c).mp hc
  rw [G.defectPlaneFaces_eq_empty_of_defect_free ht hf] at he
  exact Finset.notMem_empty _ he

theorem PennyGraph.ordinaryTrackComponents_eq_univ_of_defect_free {n : ℕ}
    (G : PennyGraph n) (ht : G.TriangleFree) (hf : G.faceDefectCount ht=0) :
    G.ordinaryTrackComponents=Finset.univ := by
  have h := G.ordinary_union_terminal
  rwa [G.terminalTrackComponents_eq_empty_of_defect_free ht hf,Finset.union_empty] at h

theorem PennyGraph.canonical_quadratic_bound_defect_free {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hf : G.faceDefectCount ht=0) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound := by
  let D := componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)
  have hp : D.p=0 := by
    rw [G.componentSystem_terminal_count,
      G.terminalTrackComponents_eq_empty_of_defect_free ht hf,Finset.card_empty]
  have hterm : D.terminal=∅ := Finset.card_eq_zero.mp hp
  have hr : D.r=0 := by simp [TrackSystem.r,hterm,TrackSystem.internal]
  have hd : D.defects=0 := hf
  change 10000*((D.r : ℤ)+D.defects)≤2379*D.K^2
  rw [hr,hd,TrackSystem.K,hp,hd]
  norm_num

end Swanepoel
