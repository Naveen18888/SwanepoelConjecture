module
public import Swanepoel.DefectConeCount
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def HalfOpen120Cone (b x : Plane) : Prop :=
  (1/2:ℝ) < inner ℝ b x ∨ (inner ℝ b x=1/2 ∧ 0<cross2 b x)

theorem balanced_unit_half_open_120_cone_count {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (normal : ι→Plane) (hnorm : ∀ i∈Q,‖normal i‖=1)
    (hsum : ∑ i∈Q,normal i=0) (b : Plane) (hb : ‖b‖=1) (hQ : 6≤Q.card) :
    (Q.filter (fun i => HalfOpen120Cone b (normal i))).card+3≤Q.card := by
  let P := Q.filter (fun i => HalfOpen120Cone b (normal i))
  have hPQ : P⊆Q := Finset.filter_subset _ _
  have hcone (i : ι) (hi : i∈P) : (1/2:ℝ) ≤ inner ℝ b (normal i) := by
    rcases (Finset.mem_filter.mp hi).2 with h | h
    · exact h.le
    · exact h.1.ge
  have hproj := balanced_unit_subset_projection Q P hPQ normal b (1/2) hb hnorm hsum hcone
  by_contra hn
  change ¬P.card+3≤Q.card at hn
  have hcount : 3*P.card≤2*Q.card := by
    exact_mod_cast (show (3:ℝ)*P.card≤2*Q.card by nlinarith [hproj])
  have hq : Q.card=6 := by omega
  have hp : P.card=4 := by omega
  have ho : (Q\P).card=2 := by
    have hc := Finset.card_sdiff_add_card_eq_card hPQ
    omega
  let lower (i : ι) : ℝ := if i∈P then 1/2 else -1
  have hle (i : ι) (hi : i∈Q) : lower i ≤ inner ℝ b (normal i) := by
    by_cases h : i∈P
    · simpa only [lower,ite_eq_left h] using hcone i h
    · have hbound := abs_real_inner_le_norm b (normal i)
      rw [hb,hnorm i hi,mul_one] at hbound
      simpa only [lower,ite_eq_right h] using (abs_le.mp hbound).1
  have hLP : (∑ i∈P,lower i)=2 := by
    calc
      _ = ∑ _∈P,(1/2:ℝ) := Finset.sum_congr rfl (fun i hi => by simp only [lower,ite_eq_left hi])
      _ = _ := by simp [hp]; norm_num
  have hLO : (∑ i∈Q\P,lower i)= -2 := by
    calc
      _ = ∑ _∈Q\P,(-1:ℝ) := Finset.sum_congr rfl (fun i hi => by
        simp only [lower,ite_eq_right (Finset.mem_sdiff.mp hi).2])
      _ = _ := by simp [ho]
  have hL : (∑ i∈Q,lower i)=0 := by
    have h := Finset.sum_sdiff (f := lower) hPQ
    rw [hLP,hLO] at h
    linarith
  have hpr : (∑ i∈Q,inner ℝ b (normal i))=0 := by
    rw [← inner_sum,hsum,inner_zero_right]
  have heq (i : ι) (hi : i∈Q) : inner ℝ b (normal i)=lower i := by
    have hz : (∑ j∈Q,(inner ℝ b (normal j)-lower j))=0 := by
      rw [Finset.sum_sub_distrib,hpr,hL,sub_self]
    exact sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => sub_nonneg.mpr (hle j hj))).mp hz i hi)
  have hcrossP (i : ι) (hi : i∈P) : 0<cross2 b (normal i) := by
    have hd := heq i (hPQ hi)
    simp only [lower,ite_eq_left hi] at hd
    rcases (Finset.mem_filter.mp hi).2 with h | h
    · linarith
    · exact h.2
  have hcrossO (i : ι) (hi : i∈Q\P) : cross2 b (normal i)=0 := by
    have hd := heq i (Finset.mem_sdiff.mp hi).1
    simp only [lower,ite_eq_right (Finset.mem_sdiff.mp hi).2] at hd
    have hg := cross2_sq_add_inner_sq b (normal i)
    rw [hb,hnorm i (Finset.mem_sdiff.mp hi).1,hd] at hg
    nlinarith [sq_nonneg (cross2 b (normal i))]
  have hpos : 0<∑ i∈P,cross2 b (normal i) :=
    Finset.sum_pos hcrossP (Finset.card_pos.mp (by omega))
  have hzeroO : (∑ i∈Q\P,cross2 b (normal i))=0 :=
    Finset.sum_eq_zero hcrossO
  have hzero : (∑ i∈Q,cross2 b (normal i))=0 := by
    change (∑ i∈Q,crossLinear b (normal i))=0
    rw [← map_sum,hsum,map_zero]
  have h := Finset.sum_sdiff (f := fun i => cross2 b (normal i)) hPQ
  rw [hzeroO,hzero,zero_add] at h
  linarith

theorem PennyGraph.large_defect_half_open_120_cone_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hsize : 6≤(G.faceSourcePorts F).card) (b : Plane) (hb : ‖b‖=1) :
    ((G.faceSourcePorts F).filter (fun e => HalfOpen120Cone b (sourceNormal e))).card+3≤
      (G.faceSourcePorts F).card :=
  balanced_unit_half_open_120_cone_count _ sourceNormal (fun e _ => sourceNormal_norm e)
    (G.defect_all_source_normals_sum ht F hF) b hb hsize

end Swanepoel
