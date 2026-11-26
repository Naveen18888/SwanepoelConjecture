module
public import Swanepoel.L38SupportAreaPolygon
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
attribute [local instance] Classical.propDecidable

def l38SupportAxis : Plane := cartPoint 1 0
def l38CertificateBody : Set Plane := l38SupportBody (l38BankArc l38SupportAxis) (1/3)

theorem l38_cartPoint_norm_sq (x y : ℝ) : ‖cartPoint x y‖^2=x^2+y^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [cartPoint,Fin.sum_univ_two]

theorem l38_bank_normal_coordinates {n : Plane} (hn : n∈l38BankArc l38SupportAxis) :
    (433/500:ℝ) ≤ n 0 ∧ |n 1| ≤ 1/2 := by
  have hnx : Real.sqrt 3/2 ≤ n 0 := by
    simpa [l38SupportAxis,cartPoint,PiLp.inner_apply,Fin.sum_univ_two] using hn.2
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hs0 := Real.sqrt_nonneg (3:ℝ)
  have hroot : (433/250:ℝ) ≤ Real.sqrt 3 := by nlinarith only [hs,hs0]
  have hnorm : (n 0)^2+(n 1)^2=1 := by
    have hh := EuclideanSpace.real_norm_sq_eq n
    rw [hn.1] at hh
    simpa [Fin.sum_univ_two] using hh.symm
  have hnx0 : 0 ≤ n 0 := by linarith only [hnx,hs0]
  have hx2 := (sq_le_sq₀ (show 0≤Real.sqrt 3/2 by positivity) hnx0).mpr hnx
  constructor
  · linarith only [hnx,hroot]
  · apply (sq_le_sq₀ (abs_nonneg (n 1)) (by norm_num : (0:ℝ)≤1/2)).mp
    rw [sq_abs]
    nlinarith only [hx2,hnorm,hs]

theorem l38_left_point_mem {x y : ℝ} (hx : x≤0) (hunit : x^2+y^2≤1)
    (hsupport : (433/500:ℝ)*x+|y|/2≤1/3) : cartPoint x y∈l38CertificateBody := by
  constructor
  · have heq := l38_cartPoint_norm_sq x y
    nlinarith only [heq,hunit,norm_nonneg (cartPoint x y)]
  · intro n hn
    obtain ⟨hnx,hny⟩ := l38_bank_normal_coordinates hn
    have hxbound := mul_le_mul_of_nonpos_left hnx hx
    have hybound := mul_le_mul_of_nonneg_left hny (abs_nonneg y)
    have hyinner : y*n 1 ≤ |y| * |n 1| := by
      simpa only [abs_mul] using le_abs_self (y*n 1)
    have hinner : inner ℝ (cartPoint x y) n=x*n 0+y*n 1 := by
      simp [cartPoint,PiLp.inner_apply,Fin.sum_univ_two]
      ring
    rw [hinner]
    nlinarith only [hxbound,hybound,hyinner,hsupport]

theorem l38_central_point_mem {x y : ℝ} (hsmall : x^2+y^2≤1/9) :
    cartPoint x y∈l38CertificateBody := by
  apply closedBall_subset_l38SupportBody (l38BankArc l38SupportAxis)
    (fun _ hn => hn.1) (by norm_num) (by norm_num)
  rw [Metric.mem_closedBall,dist_zero_right]
  have heq := l38_cartPoint_norm_sq x y
  nlinarith only [heq,hsmall,norm_nonneg (cartPoint x y)]

def l38RationalBack (t : ℚ) : ℚ×ℚ := ((t^2-1)/(t^2+1),2*t/(t^2+1))
def l38RationalFront (t : ℚ) : ℚ×ℚ := ((1-t^2)/(3*(t^2+1)),2*t/(3*(t^2+1)))

def l38RationalUpperTail : List (ℚ×ℚ) :=
  (List.range 16).map (fun j => l38RationalBack (((j:ℚ)+1)/20)) ++
    [l38RationalBack (831/1000),l38RationalFront (4/15),l38RationalFront (1/5),
      l38RationalFront (2/15),l38RationalFront (1/15),l38RationalFront 0]

def l38UpperTail : List (ℝ×ℝ) :=
  l38RationalUpperTail.map (fun p => ((p.1:ℝ),(p.2:ℝ)))

def l38RationalVertexGood (p : ℚ×ℚ) : Prop :=
  0≤p.2 ∧ ((p.1≤0 ∧ p.1^2+p.2^2≤1 ∧ (433/500:ℚ)*p.1+p.2/2≤1/3) ∨
    p.1^2+p.2^2≤1/9)

theorem l38_rational_vertices_good :
    ∀ p∈((-1,0):ℚ×ℚ)::l38RationalUpperTail,l38RationalVertexGood p := by
  norm_num [l38RationalUpperTail,l38RationalBack,l38RationalFront,l38RationalVertexGood,
    List.range_succ]

theorem l38_good_vertex_mem (p : ℚ×ℚ) (hp : l38RationalVertexGood p) :
    cartPoint (p.1:ℝ) (p.2:ℝ)∈l38CertificateBody ∧
      cartPoint (p.1:ℝ) (-(p.2:ℝ))∈l38CertificateBody := by
  have hy : 0≤(p.2:ℝ) := by exact_mod_cast hp.1
  rcases hp.2 with hleft | hcenter
  · have hx : (p.1:ℝ)≤0 := by exact_mod_cast hleft.1
    have hunit : (p.1:ℝ)^2+(p.2:ℝ)^2≤1 := by exact_mod_cast hleft.2.1
    have hb : (433/500:ℝ)*(p.1:ℝ)+(p.2:ℝ)/2≤1/3 := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hleft.2.2
      norm_num at hh
      exact hh
    constructor
    · apply l38_left_point_mem hx hunit
      simpa only [abs_of_nonneg hy] using hb
    · apply l38_left_point_mem hx (by simpa only [neg_sq] using hunit)
      simpa only [abs_neg,abs_of_nonneg hy] using hb
  · have hunit : (p.1:ℝ)^2+(p.2:ℝ)^2≤1/9 := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hcenter
      norm_num at hh
      exact hh
    exact ⟨l38_central_point_mem hunit,l38_central_point_mem (by simpa only [neg_sq] using hunit)⟩

theorem l38_upper_chain : l38SliceChain (-1,0) l38UpperTail := by
  norm_num [l38UpperTail,l38RationalUpperTail,l38RationalBack,l38RationalFront,
    l38SliceChain,List.range_succ]

theorem l38_upper_end : l38SliceEnd (-1,0) l38UpperTail=(1/3,0) := by
  norm_num [l38UpperTail,l38RationalUpperTail,l38RationalBack,l38RationalFront,
    l38SliceEnd,List.range_succ]

def l38CertificateHeight : ℝ→ℝ := l38SliceHeight (-1,0) l38UpperTail
def l38CertificateArea : ℝ := 2*l38SliceTrapezoids (-1,0) l38UpperTail

theorem l38_certificate_area_threshold : (1757/1000:ℝ) ≤ l38CertificateArea := by
  norm_num [l38CertificateArea,l38SliceTrapezoids,l38UpperTail,l38RationalUpperTail,
    l38RationalBack,l38RationalFront,List.range_succ]

theorem l38_certificate_height_continuous : Continuous l38CertificateHeight :=
  l38SliceHeight_continuous _ _ l38_upper_chain

theorem l38_certificate_height_integral :
    2*(∫ x in (-1:ℝ)..(1/3:ℝ),l38CertificateHeight x)=l38CertificateArea := by
  have h := l38SliceHeight_integral (-1,0) l38UpperTail l38_upper_chain
  rw [l38_upper_end] at h
  exact congrArg (fun t : ℝ => 2*t) h

theorem l38_certificate_vertices_support :
    ∀ p∈((-1,0):ℝ×ℝ)::l38UpperTail,
      cartPoint p.1 p.2∈l38CertificateBody ∧ cartPoint p.1 (-p.2)∈l38CertificateBody := by
  intro p hp
  have hmap : ((-1,0):ℝ×ℝ)::l38UpperTail =
      (((-1,0):ℚ×ℚ)::l38RationalUpperTail).map (fun q => ((q.1:ℝ),(q.2:ℝ))) := by
    simp [l38UpperTail]
  rw [hmap,List.mem_map] at hp
  obtain ⟨q,hq,rfl⟩ := hp
  exact l38_good_vertex_mem q (l38_rational_vertices_good q hq)

theorem l38_certificate_graphs_support {x : ℝ} (hx : x∈Icc (-1) (1/3)) :
    cartPoint x (l38CertificateHeight x)∈l38CertificateBody ∧
      cartPoint x (-l38CertificateHeight x)∈l38CertificateBody := by
  have hx' : x∈Icc ((-1,0):ℝ×ℝ).1 (l38SliceEnd (-1,0) l38UpperTail).1 := by
    simpa only [l38_upper_end] using hx
  constructor
  · simpa only [one_mul,l38CertificateHeight] using l38SliceHeight_graph_mem l38CertificateBody
      (l38SupportBody_convex _ _) (-1,0) l38UpperTail l38_upper_chain 1
      (fun p hp => by simpa only [one_mul] using (l38_certificate_vertices_support p hp).1) hx'
  · simpa only [neg_one_mul,l38CertificateHeight] using l38SliceHeight_graph_mem l38CertificateBody
      (l38SupportBody_convex _ _) (-1,0) l38UpperTail l38_upper_chain (-1)
      (fun p hp => by simpa only [neg_one_mul] using (l38_certificate_vertices_support p hp).2) hx'

theorem l38_certificate_vertices_nonneg :
    ∀ p∈((-1,0):ℝ×ℝ)::l38UpperTail,0≤p.2 := by
  intro p hp
  have hmap : ((-1,0):ℝ×ℝ)::l38UpperTail =
      (((-1,0):ℚ×ℚ)::l38RationalUpperTail).map (fun q => ((q.1:ℝ),(q.2:ℝ))) := by
    simp [l38UpperTail]
  rw [hmap,List.mem_map] at hp
  obtain ⟨q,hq,rfl⟩ := hp
  change 0≤(q.2:ℝ)
  exact Rat.cast_nonneg.mpr (l38_rational_vertices_good q hq).1

theorem l38_certificate_height_nonneg {x : ℝ} (hx : x∈Icc (-1) (1/3)) :
    0≤l38CertificateHeight x := by
  have hC : Convex ℝ {p : Plane | 0≤p 1} := by
    intro p hp q hq a b ha hb _hab
    change 0≤a*p 1+b*q 1
    exact add_nonneg (mul_nonneg ha hp) (mul_nonneg hb hq)
  have hx' : x∈Icc ((-1,0):ℝ×ℝ).1 (l38SliceEnd (-1,0) l38UpperTail).1 := by
    simpa only [l38_upper_end] using hx
  simpa only [Set.mem_ofPred_eq,one_mul,cartPoint_one,l38CertificateHeight] using
    l38SliceHeight_graph_mem {p : Plane | 0≤p 1} hC (-1,0) l38UpperTail l38_upper_chain 1
      (fun p hp => by simpa only [Set.mem_ofPred_eq,one_mul,cartPoint_one] using
        l38_certificate_vertices_nonneg p hp) hx'

end Swanepoel
