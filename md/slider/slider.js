'use strict';

const e = React.createElement;
const converter = new showdown.Converter({tables: true});

class Thumbnail extends React.PureComponent {

  constructor(props) {
    super(props);
    this.go = this.go.bind(this);
  }

  go() {
    if (typeof this.props.go === 'function') {
      this.props.go(this.props.id);
    }
  }

  render() {
    let classes = "title";
    if (this.props.active) {
      classes += " active-title";
    }
    return React.createElement(
      'div',
      { onClick: this.go,
        className: classes },
      this.props.title
    );
  }

}

class Slide extends React.PureComponent {

  constructor(props) {
    super(props);
  }

  render() {
    let classes = "markdown-body slide";
    if (this.props.active) {
      classes += " active-slide";
    }
    return React.createElement('div', { className: classes,
      dangerouslySetInnerHTML: { __html: converter.makeHtml(this.props.content) } });
  }

}

class Deck extends React.PureComponent {

  constructor(props) {
    super(props);
    this.switch = this.switch.bind(this);
  }

  switch() {
    if (typeof this.props.switch === 'function') {
      this.props.switch(this.props.id);
    }
  }

  render() {
    let classes = "deck";
    if (this.props.active) {
      classes += " active-deck";
    }
    return React.createElement(
      'div',
      { onClick: this.switch,
        className: classes },
      React.createElement(
        'span',
        null,
        this.props.id + 1,
        ': ',
        this.props.title
      )
    );
  }

}

class Slider extends React.Component {

  constructor(props) {

    super(props);

    let slide = parseInt(Cookies.get("slide"));
    let deck = parseInt(Cookies.get("deck"));
    let sb = Cookies.get("sidebar");

    slide = slide ? slide : 0;
    deck = deck ? deck : 0;
    sb = sb ? sb : "decks";

    this.state = {
      error: null,
      isLoaded: false,
      items: [],
      slide: slide,
      deck: deck,
      fullscreen: false,
      sidebar: sb
    };

    this.forward = this.forward.bind(this);
    this.reverse = this.reverse.bind(this);
    this.go = this.go.bind(this);
    this.switch_deck = this.switch_deck.bind(this);
    this.fullscreen = this.fullscreen.bind(this);
    this.handleKeyDown = this.handleKeyDown.bind(this);
    this.scroll_animation = null;
  }

  componentDidMount() {
    fetch("/slider/config.json").then(result => result.json()).then(config => {
      this.config = config;
      return fetch(config.slide_decks[this.state.deck].path);
    }).then(res => res.text()).then(result => {
      let slides = this.parse(result);
      let titles = slides.map(s => s.split("===")[0]);
      this.setState({
        isLoaded: true,
        slides: slides,
        titles: titles
      });
    }, error => {
      this.setState({
        isLoaded: true,
        error
      });
    });
  }

  parse(text) {
    let text1 = text.replace(/--hide[\s\S]*?--unhide/g, '');
    let text2 = text1.replace(/--brief[\s\S]*?--unbrief/g, '    ...');
    let lines = text2.split("\n");
    let sections = [];
    let i = 1;
    let section = "";
    while (i < lines.length) {
      if (i + 2 < lines.length && lines[i + 1] == "===") {
        if (section != "") {
          sections.push(section);
        }
        section = "";
      }
      section += lines[i] + "\n";
      i++;
    }
    sections.push(section);
    return sections;
  }

  forward() {
    if (this.state.slide < this.state.slides.length - 1) {
      Cookies.set("slide", this.state.slide + 1);
      this.setState({ slide: this.state.slide + 1 });
    }
  }

  reverse() {
    if (this.state.slide > 0) {
      Cookies.set("slide", this.state.slide - 1);
      this.setState({ slide: this.state.slide - 1 });
    }
  }

  go(n) {
    Cookies.set("slide", n);
    this.setState({ slide: n });
  }

  switch_deck(n) {
    Cookies.set("deck", n);
    Cookies.set("slide", 0);
    Cookies.set("sidebar", "slides");
    this.setState({ deck: n, slide: 0, sidebar: "slides" });
    this.componentDidMount();
  }

  fullscreen() {
    this.state.fullscreen ? document.webkitExitFullscreen() : document.documentElement.webkitRequestFullscreen();
    this.setState({ fullscreen: !this.state.fullscreen });
  }

  handleKeyDown(event) {
    if (this.scroll_animation == null) {
      if (event.key == "ArrowRight") {
        this.forward();
      } else if (event.key == "ArrowLeft") {
        this.reverse();
      }
    }
  }

  buttons(props) {
    return React.createElement(
      'div',
      null,
      React.createElement(
        'button',
        { id: 'forward-button',
          onClick: this.forward,
          disabled: this.state.slide == this.state.slides.length - 1 },
        '\u23F5'
      ),
      React.createElement(
        'button',
        { id: 'reverse-button',
          onClick: this.reverse,
          disabled: this.state.slide == 0 },
        '\u23F4'
      ),
      React.createElement(
        'button',
        { id: 'expand-button',
          onClick: this.fullscreen },
        '\u25F3'
      ),
      React.createElement(
        'button',
        { id: 'sidebar-button',
          onClick: () => {
            let sb = this.state.sidebar == "decks" ? "slides" : "decks";
            this.setState({ sidebar: sb });
            Cookies.set("sidebar", sb);
          } },
        this.state.sidebar != "decks" ? "Chapters" : "Slides"
      )
    );
  }

  render() {
    const { error, isLoaded, slides, titles } = this.state;
    if (error) {
      return React.createElement(
        'div',
        null,
        'Error: ',
        error.message
      );
    } else if (!isLoaded) {
      return React.createElement(
        'div',
        null,
        'Loading...'
      );
    } else {
      return React.createElement(
        'div',
        { tabIndex: '0', onKeyDown: this.handleKeyDown, className: 'slider-container' },
        React.createElement(
          'div',
          { className: 'sidebar' },
          React.createElement(
              'div',
              { style: { 
                display: this.state.sidebar == "slides" ? 'block' : 'none'}, 
                className: "deck-title",
                onClick: () => {
                  let sb = this.state.sidebar == "decks" ? "slides" : "decks";
                 this.setState({ sidebar: sb });
                 Cookies.set("sidebar", sb);
              } },
              (this.state.deck+1) + ". " + this.config.slide_decks[this.state.deck].title
            ),
          React.createElement(
            'div',
            { style: { display: this.state.sidebar == "slides" ? 'block' : 'none' } },
            titles.flatMap((t, i) => React.createElement(Thumbnail, { key: i, id: i, title: t,
              active: this.state.slide == i,
              go: this.go }))
          ),
          React.createElement(
            'div',
            { style: { display: this.state.sidebar == "decks" ? 'block' : 'none' } },
            this.config.slide_decks.flatMap((d, i) => React.createElement(Deck, { key: i, id: i, title: d.title,
              active: this.state.deck == i,
              'switch': this.switch_deck }))
          )
        ),
        React.createElement(
          'div',
          { className: 'slides-container' },
          slides.flatMap((s, i) => React.createElement(Slide, { key: i, id: i, content: s, 'switch': this.switch_deck,
            active: this.state.slide == i })),
          this.buttons()
        )
      );
    }
  }

  componentDidUpdate() {

    document.querySelectorAll('pre code').forEach(block => {
      hljs.highlightBlock(block);
    });

    if (this.state.sidebar == "slides") {

      let sidebar = document.querySelectorAll('.sidebar')[0];
      let active_thumb = document.querySelectorAll('.active-title')[0];
      let initial = sidebar.scrollTop;
      let target = Math.max(active_thumb.offsetTop - sidebar.clientHeight / 2, 0);
      let current = initial;
      let t = 0,
          T = 1 * Math.abs(target - initial);
      const DT = 5;

      if (this.scroll_animation != null) {
        clearInterval(this.scroll_animation);
        this.scroll_animation = null;
      }

      this.scroll_animation = setInterval(() => {
        let p = t / T;
        current = p * target + (1 - p) * initial;
        sidebar.scrollTo(0, current);
        t += DT;
        if (t >= T) {
          clearInterval(this.scroll_animation);
          this.scroll_animation = null;
          sidebar.scrollTo(0, target);
        }
      }, DT);
    }
  }

}

const main = document.querySelector('#main');
ReactDOM.render(e(Slider), main);
