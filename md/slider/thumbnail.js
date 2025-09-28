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