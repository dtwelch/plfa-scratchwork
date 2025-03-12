\documentclass[a4paper]{article}
\usepackage[margin=1.85cm, paperwidth=7.1in, paperheight=9in, bottom=2.5cm]{geometry}
\usepackage[parfill]{parskip}

\usepackage{mathptmx}  
\usepackage{xcolor}
\usepackage{newtxtext}
\definecolor{customgray}{gray}{0.099}  
\color{customgray}     

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{amssymb} \usepackage{stmaryrd} \usepackage{csquotes}
\usepackage{unicode-math}
\usepackage{newunicodechar}
\usepackage{listings}
\usepackage{mathptmx}
\usepackage[colorlinks = true,
            linkcolor = black,
            urlcolor  = blue,
            citecolor = black
            anchorcolor = black]{hyperref}

\lstset{
basicstyle=\ttfamily,
columns=fullflexible,
keepspaces=true,
breaklines=true,
mathescape=true
}
\usepackage[links]{agda}
\usepackage{mathpartir} %inf rules

%\setmathfont{XITS Math}
\newunicodechar{α}{\ensuremath{\mathnormal\alpha}}
\newunicodechar{β}{\ensuremath{\mathnormal\beta}}
\newunicodechar{η}{\ensuremath{\mathnormal\eta}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{Λ}{\ensuremath{\mathnormal\Lambda}}
\newunicodechar{π}{\ensuremath{\mathnormal\pi}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal\upphi}}
\newunicodechar{←}{\ensuremath{\mathnormal\from}}
\newunicodechar{→}{\ensuremath{\mathnormal\to}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{↦}{\ensuremath{\mathnormal\mapsto}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{₄}{\ensuremath{\mathnormal{_4}}}
\newunicodechar{₅}{\ensuremath{\mathnormal{_5}}}
\newunicodechar{₆}{\ensuremath{\mathnormal{_6}}}
\newunicodechar{₇}{\ensuremath{\mathnormal{_7}}}
\newunicodechar{₈}{\ensuremath{\mathnormal{_8}}}
\newunicodechar{₉}{\ensuremath{\mathnormal{_9}}}
\newunicodechar{𝓤}{\ensuremath{\mathnormal{\mathscr{U}}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{⇀}{\ensuremath{\mathnormal\rightharpoonup}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ᵣ}{\ensuremath{\mathnormal{_r}}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{′}{\ensuremath{\mathnormal\prime}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⦂}{\ensuremath{\mathnormal{:}}}
\newunicodechar{₍}{\ensuremath{\mathnormal{(}}}
\newunicodechar{₎}{\ensuremath{\mathnormal{)}}}
\newunicodechar{≣}{\ensuremath{\mathnormal\Xi}}
\newunicodechar{ƛ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{≟}{\ensuremath{\mathnormal=?}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{∷}{\ensuremath{\mathnormal::}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{∨}{\ensuremath{\mathnormal\lor}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^b}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{\mid}}}

\title{Part 1.02: Induction}
\author{}

\begin{document}

\maketitle

\section*{Prelude}

Here is our top level module name:
\begin{code}
module src.part1.induction-p01-02 where
\end{code}
We'll need the following imports:
\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using(begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
\end{code}

\section{Induction}

To prove a property of natural numbers by induction, we need to prove two cases.
First is the base case, where we show the property holds for `zero'.

Second is the inductive case, where we assume the property holds for an arbitrary
natural number \texttt{m} (we call this the inductive hypothesis), and then show the 
property must also hold for \texttt{(suc m)}.

There are two inference rules for natural numbers (these are given by the inductive
type definition): s

\begin{lstlisting}
---------
P zero

P m
---------
P (suc m)
\end{lstlisting}

\subsubsection*{First proof: associativity}

To prove associativity, take \texttt{P m} to be the property:
\begin{lstlisting}
(m + n) + p $\equiv$ m + (n + p)
\end{lstlisting}

If we can demonstrate that both the base case and inductive case hold, then 
associativity of addition follows by induction.
% _+_ : ℕ -> ℕ ­-> ℕ
% _+_ zero n    = n 
% _+_ (suc m) n = suc (m + n)
Here is the proposition's statement and proof:
\begin{code}
+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc zero n p = 
    begin 
        (zero + n) + p
    ≡⟨⟩ 
        n + p
    ∎
+-assoc (suc m) n p = 
    begin 
        ((suc m) + n) + p
    ≡⟨⟩
        suc (m + n) + p
    ≡⟨ cong (suc) (+-assoc m n p) ⟩ 
        suc m + (n + p)
    ∎
\end{code}

\end{document}
