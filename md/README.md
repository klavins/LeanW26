Slider
===

Slider displays markdown files as a series of slides in the web browser. Any section of a markdown file that starts with

```markdown
A Slide Name
===
```
is considered the start of a section. 

Installation
===

- Clone this repository.
- `npm intsall`
- For now, edit slider.js with the URL of the markdown page you want to display as slides.
- Make a file called `config.json` with something like the following in it:
    ```json
    {
        "slide_decks": [
            { "path": "https://mysite.com/courses/week_1/README.md", "title": "Build Environment" },
            { "path": "https://mysite.com/courses/week_2/README.md", "title": "The C Language" }
        ]
    }
    ```
- Navigate to index.html in the repository with your browser.
- You might also want to serve the web page properly and put your markdown files within the directory being served. That way the AJAX request that Slider makes with not give you a CORS error.

Todo
===
- More configurability
- Make this whole thing easier to install and use.