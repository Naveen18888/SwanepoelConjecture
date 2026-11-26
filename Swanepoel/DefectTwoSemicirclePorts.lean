module
public import Swanepoel.FaceDirectionalSupport
public import Swanepoel.FaceBoundaryCapReduction
public import Swanepoel.FaceBoundaryOrderOrbit
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def normalTestAxis (d : Plane) : Plane →ₗ[ℝ] ℝ :=
  -((innerSL ℝ d).toLinearMap.comp rightNormalMap)

@[simp] theorem normalTestAxis_carried {n : ℕ} {G : PennyGraph n} (d : Plane)
    (e : OrientedEdge G) : normalTestAxis d (carriedVector e)= -inner ℝ d (sourceNormal e) := rfl

private theorem reverse_cell_directions {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    C.portReverse.u= -C.u ∧ C.portReverse.v=C.v := by
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  constructor
  · change G.point C.a-G.point C.b= -(G.point C.b-G.point C.a)
    abel
  · change G.point C.c-G.point C.b=G.point C.d-G.point C.a
    rw [hc]
    abel

theorem PennyGraph.defect_two_semicircle_ports {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (d : Plane) (hd : d≠0) :
    2≤((G.faceSourcePorts F).filter (fun e => 0 < inner ℝ d (sourceNormal e))).card := by
  let P := (G.faceSourcePorts F).filter (fun e => 0 < inner ℝ d (sourceNormal e))
  change 2≤P.card
  by_contra hn
  have hcard : P.card≤1 := by omega
  obtain ⟨initial,hinitial,hpositive⟩ := G.defect_meets_semicircle ht F hF d hd
  have hiP : initial∈P := Finset.mem_filter.mpr ⟨hinitial,hpositive⟩
  have hunique : ∀ e∈G.faceSourcePorts F, 0 < inner ℝ d (sourceNormal e) → e=initial := by
    intro e he hpos
    exact Finset.card_le_one.mp hcard e (Finset.mem_filter.mpr ⟨he,hpos⟩) initial hiP
  have hface : G.sourceFace initial=F := (Finset.mem_filter.mp hinitial).2.2
  have hsource : SpineSource initial := (Finset.mem_filter.mp hinitial).2.1
  have hnegative : normalTestAxis d (carriedVector initial)<0 := by
    rw [normalTestAxis_carried]
    linarith
  have huniqueNeg : ∀ e∈G.faceSourcePorts F, normalTestAxis d (carriedVector e)<0 → e=initial := by
    intro e he hneg
    apply hunique e he
    rw [normalTestAxis_carried] at hneg
    linarith
  obtain ⟨C,last,hfirst,hlast,hlastFace,_⟩ :=
    G.unique_negative_port_forces_cap_rhombus ht F hF hdegree initial hface
      (normalTestAxis d) hnegative huniqueNeg
  have hsupport := G.unique_positive_defect_port_right_support ht F hF d hd initial hunique
  have hlastClosure := (G.sourceFace_endpoints_mem_closure last).1
  have hcClosure : G.point C.c∈closure F.val := by
    simpa only [hlast,hlastFace] using hlastClosure
  have hs := hsupport (G.point C.c) hcClosure
  have hbc : G.point C.c-G.point C.b=C.v := by
    have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
      (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
    dsimp [RhombusCell.v]
    rw [hc]
    abel
  have hu : G.point C.a-G.point C.b= -C.u := by
    dsimp [RhombusCell.u]
    abel
  simp only [carriedVector,hfirst] at hs
  rw [hu,hbc,cross2_neg_left] at hs
  have hnonneg : 0≤cross2 C.u C.v := by linarith
  have hpos : 0<cross2 C.u C.v :=
    lt_of_le_of_ne hnonneg (Ne.symm (C.cross_ne_zero ht))
  obtain ⟨hru,hrv⟩ := reverse_cell_directions C
  have hneg : cross2 C.portReverse.u C.portReverse.v<0 := by
    rw [hru,hrv,cross2_neg_left]
    linarith
  have hlabel : initial.val=(C.portReverse.a,C.portReverse.b) := hfirst
  have hrhombus := G.sourceFace_eq_rhombus_of_negative_ab ht initial C.portReverse hlabel hneg
  exact G.sourceFace_ne_rhombus ht initial hsource C.portReverse hrhombus

theorem PennyGraph.defect_two_semicircle_ports_of_delete_connected {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hn : 3≤n)
    (hdelete : ∀ a : Fin n, (G.graph.induce {w | w≠a}).Connected)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (d : Plane) (hd : d≠0) :
    2≤((G.faceSourcePorts F).filter (fun e => 0 < inner ℝ d (sourceNormal e))).card :=
  G.defect_two_semicircle_ports ht F hF (G.other_neighbor_of_delete_connected hn hdelete) d hd

end Swanepoel
