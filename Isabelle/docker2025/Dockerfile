# Isabelle2025-2 (the AFP release) with a LaTeX installation, to build AFP-style documents (document=pdf).
FROM makarius/isabelle:Isabelle2025-2
USER root
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      texlive-latex-base texlive-latex-recommended texlive-latex-extra texlive-fonts-recommended \
      texlive-science texlive-bibtex-extra texlive-plain-generic lmodern && rm -rf /var/lib/apt/lists/*
USER isabelle
