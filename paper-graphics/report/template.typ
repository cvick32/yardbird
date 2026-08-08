#set page(
  paper: "us-letter",
  margin: (x: 0.8in, y: 0.75in),
)

#set text(size: 10.5pt)
#set par(justify: true, leading: 0.75em)
#set heading(numbering: "1.")
#set figure.caption(position: bottom)

#show heading.where(level: 1): it => block(
  width: 100%,
  inset: (top: 0.75em, bottom: 0.5em),
)[
  #text(size: 17pt, weight: "bold")[#it.body]
]
