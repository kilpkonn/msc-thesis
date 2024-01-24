// The project function defines how your document looks.
// It takes your content and some metadata and formats it.
// Go ahead and customize it to your liking!
#let project(
  title: "",
  title_estonian: "",
  thesis_type: "",
  abstract: [],
  authors: (),
  supervisors: (),
  date: none,
  location: "",
  logo: none,
  body,
) = {
  // Set the document's basic properties.
  let doc_authors = authors.map(author => author.name)
  set document(author: doc_authors, title: title)
  set text(font: "New Computer Modern", lang: "en")
  show math.equation: set text(weight: 400)
  set heading(numbering: "1.1")

  // Title page.
  // The page can contain a logo if you pass one with `logo: "logo.png"`.
  v(0.6fr)
  if logo != none {
    align(right, image(logo, width: 26%))
  }
  v(1.2fr)
  
  v(1.2em, weak: true)
  align(center, text(2em, weight: 700, title))
  v(1.2em, weak: true)
  align(center, text(2em, weight: 500, title_estonian))

  v(2.4em, weak: true)
  align(center, text(2em, weight: 300, smallcaps(thesis_type)))


  // Author information.
  pad(
    top: 0.7em,
    right: 10%,
    align(right,
      grid(
        rows: authors.len(),
        gutter: 1em,
        ..authors.map(author => align(right, 
          strong(author.name) +
          linebreak() +
          author.student_code
        )),
      ),
    )
  )

  // Supervisors
  pad(
    top: 0.7em,
    right: 10%,
    align(right,
      strong("Supervisor") +
      grid(
        rows: supervisors.len(),
        gutter: 1em,
        ..supervisors.map(supervisor => align(right, supervisor)),
      ),
    )
  )

  v(2.4fr)

  place(bottom+center)[
    #location #datetime.today().year()
  ]
  
  pagebreak()

  set page(numbering: "I", number-align: center)
  counter(page).update(1)


  // Abstract page.
  v(1fr)
align(center)[
    #heading(
      outlined: false,
      numbering: none,
      text(0.85em, smallcaps[Abstract]),
    )
    #abstract
  ]
  v(1.618fr)
  pagebreak()

  // Table of contents.
  outline(depth: 3, indent: true)
  pagebreak()

  // Abbreviations
  include("abbreviations.typ")


  // Main body.
  set par(justify: true)
  set page(numbering: "1", number-align: center)
  counter(page).update(1)

  body

  pagebreak()
  bibliography("references.bib")
}

#let todo(txt) = box[\u{1F534} #text(rgb("EE1122"))[TODO: ] #text(rgb("220099"))[#txt] ]