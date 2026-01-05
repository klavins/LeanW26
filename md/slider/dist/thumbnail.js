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

    let t = this.props.title.length > 22 
          ? this.props.title.slice(0,19) + "..."
          : this.props.title;

    if (this.props.title.includes("Exercise")) {
      classes += " exercise";
    }

    if (this.props.title.includes("div")) {
      t = "1. Under Construction";
    }    
    
    return React.createElement(
      'div',
      { onClick: this.go,
        className: classes },
      t
    );
  }

}

