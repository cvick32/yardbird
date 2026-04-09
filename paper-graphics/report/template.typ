#set page(
  paper: "us-letter",
  margin: (x: 0.8in, y: 0.75in),
)

#set text(size: 10.5pt)
#set par(justify: true, leading: 0.75em)
#set heading(numbering: "1.")
#set figure.caption(position: bottom)

#show heading.where(level: 1): it => [
  #v(0.75em)
  #text(size: 17pt, weight: "bold")[#it.body]
  #v(0.25em)
]
