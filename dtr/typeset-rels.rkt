#lang racket

(require redex "dtr-lang.rkt" "dtr-fme.rkt" "dtr-logic.rkt")

(define-judgment-form λDTR
  #:mode (Proves I I)
  #:contract (Proves Γ ψ)
  
  [(subtype (env Φ (δ_1 ... δ_2 ...) ()) o_1 τ σ)
   (lexp-equal o_1 o_2)
   ---------------- "L-Sub"
   (Proves (env Φ (δ_1 ... (o_1 ~ τ) δ_2 ...) ()) 
           (o_2 ~ σ))]
  
  [(subtype (env Φ [δ_1 ... δ_2 ...] ()) o_1 σ τ)
   (lexp-equal o_1 o_2)
   ---------------- "L-SubNot"
   (Proves (env Φ (δ_1 ... (o_1 ¬ τ) δ_2 ...) ()) 
           (o_2 ¬ σ))]
  
  [(type-conflict (env Φ () ()) τ σ)
   (lexp-equal o_1 o_2)
   ---------------- "L-Conflict"
   (Proves (env Φ (δ_1 ... (o_1 ~ τ) δ_2 ...) ()) 
           (o_2 ¬ σ))]
  
  [(fme-imp Φ Φ_1)
   ---------------- "L-FME"
   (Proves (env Φ δ* ()) 
           Φ_1)]
  
  [(where #f (fme-sat Φ))
   ---------------- "L-FME-Unsat"
   (Proves (env Φ δ* ()) 
           ψ)]
  
  [---------------------- "L-Bot"
   (Proves (env Φ (δ_1 ... (o ~ (U)) δ_2 ...) ()) 
           ψ)]
  
  [---------------------- "L-True"
   (Proves Γ TT)]
  
  [(Proves (env Φ δ* (ψ_1 ...)) 
           ψ)
   ---------------------- "L-Weaken"
   (Proves (env Φ δ* (TT ψ_1 ...)) 
           ψ)]
  
  [---------------------- "L-ExFalso"
   (Proves (env Φ δ* (FF ψ_1 ...)) 
           ψ)]
  
  [(Proves (env Φ δ* [ψ_1 ψ_2 ψ_3 ...]) 
           ψ)
   ---------------------- "L-Simp"
   (Proves (env Φ δ* ((ψ_1 ∧ ψ_2) ψ_3 ...)) 
           ψ)]
  
  [(Proves (env Φ δ* ()) ψ_1)
   (Proves (env Φ δ* ()) ψ_2)
   ---------------------- "L-Conj"
   (Proves (env Φ δ* ()) 
           (ψ_1 ∧ ψ_2))]
  
  [(Proves (env Φ δ* (ψ_1 ψ_3 ...)) 
           ψ)
   (Proves (env Φ δ* (ψ_2 ψ_3 ...)) 
           ψ)
   ---------------------- "L-DisjElim"
   (Proves (env Φ δ* ((ψ_1 ∨ ψ_2) ψ_3 ...)) 
           ψ)]
  
  [(Proves (env Φ δ* ()) ψ_1)
   ---------------------- "L-Add-L"
   (Proves (env Φ δ* ()) 
           (ψ_1 ∨ ψ_2))]
  
  [(Proves (env Φ δ* ()) 
           ψ_2)
   ---------------------- "L-Add-R"
   (Proves (env Φ δ* ()) 
           (ψ_1 ∨ ψ_2))]
  
  [(Proves (env (app Φ Φ_1) δ* (ψ_2 ψ_3 ...)) 
           ψ)
   ---------------------- "L-SLI"
   (Proves (env Φ δ* (Φ_1 ψ_2 ψ_3 ...)) 
           ψ)]
  
  [(where Φ_2 (app Φ Φ_1))
   (Proves (env Φ_2 (Φ-update-δ* δ* Φ_2) ()) 
           ψ)
   ---------------------- "L-SLI/Φ"
   (Proves (env Φ δ* (Φ_1)) 
           ψ)]
  
  [(contains-non-δ (ψ_2 ...))
   (Proves (env Φ δ* (ψ_2 ... δ_1)) 
           ψ)
   ---------------------- "L-Delay-δ"
   (Proves (env Φ δ* (δ_1 ψ_2 ...)) 
           ψ)]
  
  [(Proves (env Φ
                (ext (update-ψ* (Φ-env: Φ) δ* δ_1) δ_1)
                (update-ψ* (Φ-env: Φ) (δ_2 δ_3 ...) δ_1))
           ψ)
   ---------------------- "L-Update"
   (Proves (env Φ δ* (δ_1 δ_2 δ_3 ...)) 
           ψ)]
  
  [(Proves (env Φ
                (Φ-update-δ* (ext (update-ψ* (Φ-env: Φ) δ* δ) δ) Φ)
                ())
           ψ)
   ---------------------- "L-Update/Φ"
   (Proves (env Φ δ* (δ)) 
           ψ)])