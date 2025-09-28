
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