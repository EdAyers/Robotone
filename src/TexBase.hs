{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TexBase (
--    Tex, tex,
    texHeader, texFooter,
    math,
    escape,
    operator,
    scriptsize, footnotesize, small,
    textbf, textrm, textsc, textit,
    smalltextrm, smalltextit,
    boldmath,
    overline,
    ensuremath, texableGreekLetters,
    grey,
    texSubscript, texIntSubscript,
    texVerbatim,
    fit,
) where

import qualified Data.Set as Set

--import GHC.Unicode (isAlphaNum, isDigit)

--import Common

----------------------------------------------------------------------------------------------------
--
--class Tex a where
--    tex :: a -> String

--instance Tex Int where
--    tex = show

----------------------------------------------------------------------------------------------------

math :: String -> String
math s = "$" ++ s ++ "$"

escape :: String -> String
escape = concatMap escape'

escape' :: Char -> String
escape' '\\' = "\\ensuremath{\\backslash}"
escape' '%' = "\\%"
escape' '^' = "\\^{}"
escape' '_' = "\\_"
escape' '<' = "\\ensuremath{<}"
escape' '>' = "\\ensuremath{>}"
escape' '\'' = "\\textquotesingle{}"
escape' c = [c]

operator :: String -> String
operator s = "\\operatorname{" ++ s ++ "}"

scriptsize, footnotesize, small :: String -> String
scriptsize s = "{\\scriptsize " ++ s ++ "}"
footnotesize s = "{\\footnotesize " ++ s ++ "}"
small s = "{\\small " ++ s ++ "}"

textbf, textrm, textsc, textit :: String -> String
textbf s = "\\textbf{" ++ s ++ "}"
textrm s = "\\textrm{" ++ s ++ "}"
textsc s = "\\textsc{" ++ s ++ "}"
textit s = "\\textit{" ++ s ++ "}"

smalltextrm, smalltextit :: String -> String
smalltextrm = textrm . small
smalltextit = textit . small

boldmath s = "\\boldmath " ++ s ++ "\\unboldmath "

overline s = "\\overline{" ++ s ++ "}"

ensuremath :: String -> String
ensuremath s = "\\ensuremath{" ++ s ++ "}"

texableGreekLetters = Set.fromList
    ["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa",
     "lambda", "mu", "nu", "xi", "pi", "rho", "sigma", "tau", "upsilon", "phi", "chi", "psi",
     "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Upsilon", "Phi", "Psi"]

grey :: String -> String
grey s = "\\grey{" ++ s ++ "}"

----------------------------------------------------------------------------------------------------

texSubscript :: String -> String
texSubscript s = "_{" ++ s ++ "}"

texIntSubscript :: Int -> String
texIntSubscript = texSubscript . show

----------------------------------------------------------------------------------------------------

texVerbatim :: String -> String
texVerbatim = textbf . escape

fit :: String -> String
fit s = "\\begin{fit}" ++ s ++ "\\end{fit}"

texHeader =
    "\\documentclass[a4paper,twoside,12pt]{article}\n\
    \\\usepackage[hmargin={12mm,55mm},vmargin=10mm,footskip=7mm,asymmetric]{geometry}\n\
    \\\usepackage{amsmath}\n\
    \\\usepackage{amssymb}\n\
    \\\usepackage{tikz}\n\
    \\\usepackage{xcolor}\n\
    \\\usepackage{comment}\n\
    \\\usepackage{adjustbox}\n\
    \\\usepackage{iftex}\n\
    \\\ifPDFTeX\n\
    \\\usepackage[T1]{fontenc}\n\
    \\\usepackage[utf8]{inputenc}\n\
    \\\else\n\
    \\\usepackage[no-math]{fontspec}\n\
    \\\fi\n\
    \\\usepackage{libertine}\n\
    \\n\
    \\\makeatletter\n\
    \\\let\\_\\relax\n\
    \\\DeclareRobustCommand{\\_}{%\n\
    \  \\leavevmode\\vbox{%\n\
    \    \\hrule\\@width.4em\n\
    \          \\@height-.16ex\n\
    \          \\@depth\\dimexpr.16ex+.28pt\\relax}}\n\
    \\\makeatother\n\
    \\n\
    \\\newcommand\\Tstrut{\\rule{0pt}{2.4ex}}\n\
    \\\newcommand\\Bstrut{\\rule[-1.1ex]{0pt}{0pt}}\n\
    \\n\
    \\\tikzset{\n\
    \   tableaulabel/.style={draw=black!30, fill=gray!4, inner sep = 0.5mm, outer sep = 3mm, circle},\n\
    \   tableau/.style={draw=black!30, fill=gray!4, inner sep = 3mm, outer sep = 3mm, rounded corners=3mm, align=center},\n\
    \}\n\
    \\n\
    \\\definecolor{greycolour}{rgb}{0.6, 0.6, 0.6}\n\
    \\\newcommand\\grey[1]{{\\color{greycolour}{#1}}}\n\
    \\n\
    \\\setlength\\marginparwidth{45mm}\n\
    \\n\
    \\\newenvironment{fit}{\\begin{adjustbox}{max width=\\textwidth,max totalheight=\\textheight,keepaspectratio}}{\\end{adjustbox}}\n\
    \\n\
    \\n\
    \\\ifdefined\\showsteps\n\
    \  \\includecomment{steps}\n\
    \\\else\n\
    \  \\excludecomment{steps}\n\
    \\\fi\n\
    \\n\
    \\\raggedbottom\n\
    \\n\
    \\\begin{document}\
    \\n"

texFooter = "\n\\end{document}"

