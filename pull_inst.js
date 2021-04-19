// Run this in the browser console when the Table tab is open.
[...document.querySelectorAll(".bp3-card.bp3-elevation-1")]
  .map(
    (card) =>
      [...card.querySelectorAll(".bp3-fill")[1].childNodes].slice(-1)[0]
        .textContent +
      " = " +
      [...card.querySelector("tbody").children]
        .map((r) => [...r.children].map((c) => c.textContent).join("->"))
        .join(" + ")
  )
  .join("\n")
