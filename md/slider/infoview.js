
function goals_to_html(goals) {  

  let html = "";

  goals = eval(goals);

  if ( goals.length == 0 ) {
    html = "no goals";
  }

  for (let i=0;i<goals.length;i++) {
    let state = goals[i].split("\n");
    let turnstile = false;
    for (let j=0; j<state.length; j++) {
      if ( state[j][0] == "⊢" ) turnstile = true;
      if ( ! turnstile ) {
        state[j] = state[j].replace(/^(?!.*✝)([^:\n]+):/gm, '<span class="variable-name">$1</span>:');
        state[j] = state[j].replace(/^([^:\n]*✝[^:\n]*):/gm, '<span class="hidden-var">$1</span>:');    
      }
      state[j] = state[j].replace(/⊢/g, '<span class="turnstile">⊢</span>');
      state[j] = state[j].replace(/^case.*$/gm, (match) => `<span class="case">${match}</span>`);      
    }
    let goal = state.join("<br>");
    html += goal + "<br><br>"
  }

  return html;

}


class Infoview extends React.Component {
  constructor(props) {
    super(props);
    this.state = {
      visible: true,
    };
   // this.clear = this.clear.bind(this);
  }

//   clear() {
//     if (typeof this.props.clear === 'function') {
//       this.props.clear();
//     }
//   }

  render() {

    let classes = "infoview-container"

    if (this.props.active) {
        console.log("I'm active", this.props.id)
        classes += " active-infoview";
    }

    let button = React.createElement(
      'button',
      { onClick: this.props.clear, className : "infoview-button" },
      "×"
    );

    const popup = React.createElement(
          'div',
          { className: classes },
          button,
          React.createElement(
            'div',
             { id: 'infoview', dangerouslySetInnerHTML: { __html: goals_to_html(this.props.data) } }
          ),
        )

    return React.createElement('div', null, popup);

  }

}