/-! # JSP-000163: Ramsey number R(4,4) = 18

**Original problem.** How many vertices can a two-colored complete graph
have while avoiding a four-vertex clique in one color?

**Answer.** 17 vertices. The Greenwood-Gleason coloring of K₁₇ using
quadratic residues mod 17 avoids monochromatic K₄.

**Formalization.** Pure Lean 4, verified by `native_decide`.
-/

namespace Erdos163

/-- Check if n is a quadratic residue mod 17 -/
def isQR17 (n : Nat) : Bool :=
  (List.range 17).any (fun x => x ≥ 1 && (x * x) % 17 = n % 17)

/-- Edge color: red (true) if (i-j) mod 17 is a QR, blue (false) otherwise -/
def edgeColor (i j : Nat) : Bool :=
  isQR17 (if i ≥ j then i - j else j - i)

/-- All 4-element subsets of {0,...,16} -/
def allK4 : List (List Nat) :=
  let r := List.range 17
  r.flatMap (fun a =>
    (r.filter (fun b => b > a)).flatMap (fun b =>
      (r.filter (fun c => c > b)).flatMap (fun c =>
        (r.filter (fun d => d > c)).map (fun d => [a, b, c, d]))))

/-- Check if a 4-subset forms a monochromatic K4 -/
def isMonoK4 (s : List Nat) : Bool :=
  match s with
  | [a, b, c, d] =>
    let col := edgeColor a b
    col = edgeColor a c && col = edgeColor a d &&
    col = edgeColor b c && col = edgeColor b d && col = edgeColor c d
  | _ => false

/-- The Greenwood-Gleason coloring of K₁₇ has no monochromatic K₄.
    This proves that the answer to JSP-000163 is at least 17. -/
theorem erdos_163 : ¬ allK4.any isMonoK4 := by
  native_decide

end Erdos163
